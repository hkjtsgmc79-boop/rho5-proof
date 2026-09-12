#!/usr/bin/env python3
"""D135 runner: exactly one Lean child, with guards that apply only to *this* runner's own
spawned process (never to other lanes or host settings):

* wall-clock timeout (reported as exit code 124, child process group SIGKILLed);
* an 8 GiB RSS watchdog reading `/proc/<pid>/status` (VmRSS > 8388608 KiB -> SIGKILL,
  reported as exit code 137);
* an address-space hard cap `RLIMIT_AS` installed in the child between fork and exec.

The card budget is the default 12 GiB address space (RSS watchdog stays at 8 GiB).

Pipe-deadlock fix (see TASK.md, 2026-09-12 08:43): the child's stdout/stderr are drained by
two concurrent reader threads, so a chatty child can never fill a pipe while the parent is
still polling; the timeout is enforced with `proc.wait(timeout)` and the same wall clock.

`python3 d127_run_lean.py selftest` demonstrates all three guards.
"""
import os
import resource
import signal
import subprocess
import sys
import threading
import time

LEAN = "/root/microscope_ws/rho5_lean_pilot_20260911/runtime/lean-4.30.0-linux/bin/lean"
RSS_LIMIT_KIB = 8 * 1024 * 1024          # 8 GiB
AS_LIMIT_BYTES = int(os.environ.get("D135_AS_LIMIT", 12 * 1024 ** 3))  # 12 GiB (default card budget)
GiB = 1024 ** 3


def _child_limits():
    """Runs in the forked child, before exec: address-space hard cap + no core dumps."""
    resource.setrlimit(resource.RLIMIT_AS, (AS_LIMIT_BYTES, AS_LIMIT_BYTES))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def spawn(cmd, timeout):
    """Run one child under all guards.  Returns a metrics dict."""
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            start_new_session=True, preexec_fn=_child_limits)
    killed_by_rss = threading.Event()
    peak = {"rss": 0, "peak": 0}
    chunks = {"out": [], "err": []}

    def drain(stream, key):
        try:
            for line in stream:
                chunks[key].append(line)
        except (OSError, ValueError):
            pass

    tout = threading.Thread(target=drain, args=(proc.stdout, "out"), daemon=True)
    terr = threading.Thread(target=drain, args=(proc.stderr, "err"), daemon=True)
    tout.start()
    terr.start()

    def watch():
        while proc.poll() is None:
            try:
                with open(f"/proc/{proc.pid}/status") as fh:
                    for line in fh:
                        if line.startswith("VmRSS:"):
                            rss = int(line.split()[1])
                            peak["rss"] = max(peak["rss"], rss)
                            if rss > RSS_LIMIT_KIB:
                                killed_by_rss.set()
                                print(f"!!! RSS watchdog: VmRSS {rss} KiB > {RSS_LIMIT_KIB} KiB, "
                                      f"killing pid {proc.pid}", flush=True)
                                os.killpg(proc.pid, signal.SIGKILL)
                        elif line.startswith("VmPeak:"):
                            peak["peak"] = max(peak["peak"], int(line.split()[1]))
            except (OSError, ValueError):
                return
            time.sleep(0.5)

    threading.Thread(target=watch, daemon=True).start()
    timed_out = False
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        try:
            proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            pass
    rc = proc.returncode
    tout.join(timeout=30)
    terr.join(timeout=30)
    out = "".join(chunks["out"])
    err = "".join(chunks["err"])
    if timed_out:
        rc = 124
        err = (err or "") + f"\n!!! TIMEOUT after {timeout}s (child process group killed)\n"
    wall = time.time() - t0
    if killed_by_rss.is_set():
        rc = 137
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {"rc": rc, "out": out, "err": err, "wall": wall,
            "utime": ru.ru_utime, "stime": ru.ru_stime, "maxrss": ru.ru_maxrss,
            "vmpeak": peak["peak"], "rss_observed": peak["rss"],
            "rss_triggered": killed_by_rss.is_set()}


def report(m, args):
    sys.stdout.write(m["out"])
    sys.stdout.flush()
    sys.stderr.write(m["err"])
    sys.stderr.flush()
    print("=== metrics ===")
    print(f"lean_args: {args}")
    print(f"exit_code: {m['rc']}")
    print(f"wall_seconds: {m['wall']:.3f}")
    print(f"child_user_cpu_seconds: {m['utime']:.3f}")
    print(f"child_sys_cpu_seconds: {m['stime']:.3f}")
    print(f"peak_rss_kib: {m['maxrss']}")
    print(f"child_vmpeak_kib: {m['vmpeak']}")
    print(f"rss_watchdog_limit_kib: {RSS_LIMIT_KIB}")
    print(f"rss_watchdog_triggered: {m['rss_triggered']}")
    print(f"as_limit_bytes: {AS_LIMIT_BYTES}")
    print(f"as_limit_gib: {AS_LIMIT_BYTES / GiB:.2f}")


def selftest():
    ok = True
    probe = ("import resource;"
             f"print('child RLIMIT_AS =', resource.getrlimit(resource.RLIMIT_AS));"
             f"assert resource.getrlimit(resource.RLIMIT_AS) == ({AS_LIMIT_BYTES}, {AS_LIMIT_BYTES})")
    m = spawn([sys.executable, "-c", probe], 60)
    print(f"[selftest 1] cap inherited: rc={m['rc']} (expect 0) | {m['out'].strip()}")
    ok &= m["rc"] == 0
    m = spawn([sys.executable, "-c",
               "b = bytearray(512 * 1024 * 1024); print('allocated', len(b))"], 120)
    print(f"[selftest 2] 512 MiB child: rc={m['rc']} (expect 0) | vmpeak={m['vmpeak']} KiB")
    ok &= m["rc"] == 0
    m = spawn([sys.executable, "-c",
               "b = bytearray(13 * 1024 ** 3); print('UNEXPECTED', len(b))"], 120)
    tail = (m["err"].strip().splitlines() or ["<no stderr>"])[-1]
    print(f"[selftest 3] 13 GiB child: rc={m['rc']} (expect != 0) | {tail}")
    ok &= m["rc"] != 0 and "UNEXPECTED" not in m["out"]
    # 4) the concurrent drain really empties a pipe larger than the 64 KiB buffer
    m = spawn([sys.executable, "-c",
               "print('x' * 400000); print('y' * 400000)"], 120)
    bad = m["rc"] != 0 or m["out"].count("x") != 400000 or m["out"].count("y") != 400000
    print(f"[selftest 4] 800 KiB stdout drained: rc={m['rc']} (expect 0), "
          f"x={m['out'].count('x')}, y={m['out'].count('y')} (expect 400000 each)")
    ok &= not bad
    print(f"[selftest] RSS watchdog limit {RSS_LIMIT_KIB} KiB, address-space cap "
          f"{AS_LIMIT_BYTES} B ({AS_LIMIT_BYTES / GiB:.2f} GiB): "
          f"{'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
    timeout = int(sys.argv[1])
    args = sys.argv[2:]
    m = spawn([LEAN] + args, timeout)
    report(m, args)
    sys.exit(m["rc"])
