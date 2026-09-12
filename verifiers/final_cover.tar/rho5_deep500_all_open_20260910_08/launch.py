"""Idempotent detached launcher for this directory's coordinator, on X only."""

from __future__ import annotations

import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
COORDINATOR = ROOT / "coordinator.py"
LAUNCH = ROOT / "LAUNCH.json"


def atomic(path, value):
    temporary = path.with_name(path.name + ".tmp." + str(os.getpid()))
    with temporary.open("w") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def process_identity(pid):
    """Read PID incarnation and exact script/cwd identity, without signals."""
    proc = Path("/proc") / str(int(pid))
    try:
        fields = (proc / "stat").read_text().rsplit(")", 1)[1].strip().split()
        start = fields[19]
        state = fields[0]
    except (FileNotFoundError, ProcessLookupError):
        return None
    result = {"pid": int(pid), "start_ticks": str(start), "state": state,
              "alive": state not in ("Z", "X"), "same_coordinator": False}
    if not result["alive"]:
        return result
    try:
        argv = [part.decode("utf-8", "replace") for part in
                (proc / "cmdline").read_bytes().split(b"\0") if part]
        cwd = (proc / "cwd").resolve(strict=True)
        executable = (proc / "exe").resolve(strict=True)
        same_script = any(
            Path(arg).name == "coordinator.py"
            and ((cwd / arg) if not Path(arg).is_absolute() else Path(arg)).resolve() == COORDINATOR
            for arg in argv[1:]
        )
        result.update(cmdline=argv, cwd=str(cwd), executable=str(executable),
                      same_coordinator=(same_script and cwd == ROOT
                                        and executable == Path(sys.executable).resolve()))
    except (FileNotFoundError, ProcessLookupError):
        result["alive"] = False
    return result


def summary_status():
    try:
        data = json.loads((ROOT / "STATUS.json").read_text())
    except (OSError, ValueError):
        return None
    return {key: data[key] for key in
            ("phase", "epoch", "active_jobs", "active_workers", "worker_limit")
            if key in data and isinstance(data[key], (str, int, float, bool, type(None)))}


def result_for_existing(identity, recovered=False):
    return {"status": "ALREADY_RUNNING", "root": str(ROOT),
            "pid": identity["pid"], "start_ticks": identity["start_ticks"],
            "recovered_launch_record": recovered, "state": summary_status()}


def nice_at_least_ten():
    # The supervisor is NOT given a 4 GiB address-space limit. Each worker
    # establishes its own separate limit before importing scientific code.
    if os.getpriority(os.PRIO_PROCESS, 0) < 10:
        os.setpriority(os.PRIO_PROCESS, 0, 10)


def launch():
    if not Path("/proc/self/stat").is_file():
        raise RuntimeError("Run this launcher on X/Linux only")
    if not COORDINATOR.is_file():
        raise FileNotFoundError(str(COORDINATOR))
    # This serializes launchers only. The coordinator independently owns
    # DAEMON.lock for its full lifetime; this script never acquires that lock.
    with (ROOT / "LAUNCH.lock").open("a+") as launch_lock:
        fcntl.flock(launch_lock, fcntl.LOCK_EX)
        if LAUNCH.exists():
            old = json.loads(LAUNCH.read_text())
            identity = process_identity(old["pid"])
            if identity and identity["alive"]:
                recorded_start = old.get("start_ticks", old.get("start_tick"))
                if (str(recorded_start) == identity["start_ticks"]
                        and identity["same_coordinator"]
                        and Path(old["root"]).resolve() == ROOT):
                    return result_for_existing(identity)
                raise RuntimeError(
                    "LAUNCH.json references a live PID whose identity does not match; "
                    "preserving that record and refusing to launch or overwrite it")
        # Recover the narrow crash window after Popen but before LAUNCH.json.
        # Never replace a still-live registered PID, checked above.
        found = []
        for proc in Path("/proc").iterdir():
            if not proc.name.isdigit():
                continue
            identity = process_identity(proc.name)
            if identity and identity["alive"] and identity["same_coordinator"]:
                found.append(identity)
        if len(found) > 1:
            raise RuntimeError("Multiple matching coordinators exist; preserving all processes and records")
        if found:
            identity = found[0]
            uptime = float(Path("/proc/uptime").read_text().split()[0])
            began = time.time() - uptime + int(identity["start_ticks"]) / os.sysconf("SC_CLK_TCK")
            atomic(LAUNCH, {"pid": identity["pid"], "start_ticks": identity["start_ticks"],
                            "root": str(ROOT), "started_epoch": began,
                            "recovered_epoch": time.time(), "recovered_from_proc": True,
                            "command": identity["cmdline"]})
            return result_for_existing(identity, recovered=True)
        env = dict(os.environ)
        for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                     "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
                     "OMP_THREAD_LIMIT", "HIGHS_THREADS"):
            env[name] = "1"
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONUNBUFFERED"] = "1"
        command = [sys.executable, "-B", str(COORDINATOR)]
        began = time.time()
        with (ROOT / "DAEMON.log").open("ab", buffering=0) as log:
            child = subprocess.Popen(
                command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                close_fds=True, preexec_fn=nice_at_least_ten,
            )
        identity = process_identity(child.pid)
        record = {"pid": child.pid, "start_ticks": identity["start_ticks"] if identity else None,
                  "root": str(ROOT), "started_epoch": began, "command": command,
                  "detached": True, "nice": 10, "library_threads": 1}
        atomic(LAUNCH, record)
        exit_code = child.poll()
        if exit_code is not None or not identity or not identity["same_coordinator"]:
            return {"status": "STARTUP_FAILED_OR_EXITED", **record,
                    "returncode": exit_code, "log": str(ROOT / "DAEMON.log")}
        return {"status": "STARTED", **record,
                "state": summary_status(), "log": str(ROOT / "DAEMON.log"),
                "health_confirmed": False}


if __name__ == "__main__":
    try:
        output = launch()
        print(json.dumps(output, ensure_ascii=False, sort_keys=True))
        if output["status"] == "STARTUP_FAILED_OR_EXITED":
            raise SystemExit(1)
    except Exception as error:
        print(json.dumps({"status": "LAUNCH_REFUSED_OR_FAILED", "error": repr(error),
                          "root": str(ROOT)}, ensure_ascii=False, sort_keys=True))
        raise SystemExit(1)
