"""Conservative, Linux-only admission control; never terminates running work.

Call capacity_sample(task_root, live_worker_pids, config) before dispatch. Its
worker_limit is a TOTAL owned-worker limit, so dispatch at most dispatch_slots.
The first call (or a sampling gap above 30 s) takes a 0.25 s sample. Subsequent
calls reuse CAPACITY_STATE.json. This file is local to the new task only.

Set production_status_paths to all existing X production STATUS.json files;
an explicitly empty list disables that additional reservation. Missing required
status files fail closed for new dispatch. Existing workers always continue.

memory_admission_mode="actual_rss_incremental" admits using MemAvailable and
one configured incremental allowance per NEW group, instead of reserving each
existing worker's address-space ceiling. A separate low-memory watchdog is
required for that dynamic policy; this read-only admission sampler never pauses
or terminates workers. All worker descendants, including LP helpers, count.
"""

from __future__ import annotations

import json
import math
import os
from pathlib import Path
import resource
import time

GIB = 1024 ** 3
DEFAULT_PRODUCTION_STATUS = (
    "/root/microscope_ws/rho5_cqg_continuous_20260910/run_01/STATUS.json"
)


def _atomic(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + ".tmp." + str(os.getpid()))
    with temporary.open("w") as stream:
        json.dump(value, stream, separators=(",", ":"))
        stream.write("\n")
    os.replace(temporary, path)


def _parse_stat(text, page_size):
    # comm may itself contain spaces or parentheses.
    fields = text[text.rindex(")") + 2:].split()
    return {
        "ppid": int(fields[1]),
        "ticks": int(fields[11]) + int(fields[12]),
        "start": int(fields[19]),
        "rss": max(0, int(fields[21])) * page_size,
        "state": fields[0],
    }


def _snapshot():
    page_size = os.sysconf("SC_PAGE_SIZE")
    rows = {}
    denied = 0
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            rows[entry.name] = _parse_stat((entry / "stat").read_text(), page_size)
        except PermissionError:
            denied += 1
        except (FileNotFoundError, ProcessLookupError, ValueError, IndexError):
            # A process may exit between listing /proc and reading its stat.
            continue
    return {
        "monotonic": time.monotonic(),
        "epoch": time.time(),
        # Container-provided /proc/uptime may use a different epoch from
        # /proc/PID/stat start ticks. CLOCK_BOOTTIME shares their kernel timebase.
        "uptime": time.clock_gettime(time.CLOCK_BOOTTIME),
        "uptime_clock": "CLOCK_BOOTTIME",
        "boot_id": Path("/proc/sys/kernel/random/boot_id").read_text().strip(),
        "ticks_per_second": os.sysconf("SC_CLK_TCK"),
        "rows": rows,
        "permission_denied": denied,
    }


def _descendants(rows, roots):
    children = {}
    for pid, row in rows.items():
        children.setdefault(str(row["ppid"]), []).append(pid)
    result = set(map(str, roots)) & set(rows)
    todo = list(result)
    while todo:
        for child in children.get(todo.pop(), ()):
            if child not in result:
                result.add(child)
                todo.append(child)
    return result


def _cpu_delta(previous, current):
    dt = current["monotonic"] - previous["monotonic"]
    hz = current["ticks_per_second"]
    values = {}
    for pid, now in current["rows"].items():
        old = previous["rows"].get(pid)
        if old and old["start"] == now["start"]:
            ticks = max(0, now["ticks"] - old["ticks"])
        elif now["start"] / hz >= previous["uptime"] - 1 / hz:
            # Include processes born during the window, without charging the
            # lifetime CPU of old processes that were absent from a snapshot.
            ticks = now["ticks"]
        else:
            ticks = 0
        values[pid] = ticks / hz / dt
    return values, dt


def _read_memory():
    values = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, rest = line.split(":", 1)
        values[key] = int(rest.split()[0]) * 1024
    return values["MemAvailable"], values["MemTotal"]


def _owned_memory_groups(current, roots, incremental_memory, startup_seconds):
    """Account each descendant once, using its closest owned ancestor.

    /proc start ticks measure this process's actual age, unlike ru_maxrss, which
    may retain a pre-exec parent's high-water mark. Existing RSS is already
    deducted by MemAvailable; only a young group's unresident startup allowance
    is an additional debt.
    """
    rows = current["rows"]
    roots = set(map(str, roots)) & set(rows)
    grouped = {pid: [] for pid in roots}
    for pid in _descendants(rows, roots):
        ancestor = pid
        seen = set()
        while ancestor in rows and ancestor not in seen:
            if ancestor in roots:
                grouped[ancestor].append(pid)
                break
            seen.add(ancestor)
            ancestor = str(rows[ancestor]["ppid"])
    groups = []
    for pid in sorted(roots, key=int):
        age = max(0.0, current["uptime"] - rows[pid]["start"] / current["ticks_per_second"])
        rss = sum(rows[child]["rss"] for child in grouped[pid])
        young = age < startup_seconds
        groups.append({
            "pid": int(pid), "start_ticks": rows[pid]["start"],
            "age_seconds": age, "group_rss_bytes": rss,
            "descendant_pids": sorted(map(int, grouped[pid])),
            "within_startup_window": young,
            "startup_debt_bytes": max(0, incremental_memory - rss) if young else 0,
        })
    return groups, sum(group["startup_debt_bytes"] for group in groups)


def _production_reservation(current, cpu, excluded, config):
    paths = config.get("production_status_paths")
    if paths is None:
        paths = [config.get("production_status_path", DEFAULT_PRODUCTION_STATUS)]
    if isinstance(paths, (str, Path)):
        paths = [paths]
    rows = current["rows"]
    status_rows = []
    all_production_pids = set()
    reserved = 0.0
    blocked = False
    seen_paths = set()
    for name in paths:
        path = str(Path(name).resolve())
        if path in seen_paths:
            continue
        seen_paths.add(path)
        try:
            status = json.loads(Path(path).read_text())
            jobs = max(0, int(status["active_jobs"]))
            roots = set()
            daemon = str(status.get("daemon_pid", ""))
            expected_start = status.get("daemon_start_tick")
            daemon_live = (
                daemon in rows
                and rows[daemon]["state"] not in ("Z", "X")
                and (expected_start is None or str(rows[daemon]["start"]) == str(expected_start))
            )
            if daemon_live:
                roots.add(daemon)
            active_roots = set()
            for info in status.get("active_processes", []):
                if not isinstance(info, dict) or "pid" not in info:
                    continue
                pid = str(info["pid"])
                expected = info.get("start_tick")
                if (pid in rows and rows[pid]["state"] not in ("Z", "X")
                        and (expected is None or str(rows[pid]["start"]) == str(expected))):
                    active_roots.add(pid)
            roots.update(active_roots)
            # A dead daemon's stale active_jobs must not permanently reserve
            # cores; surviving recorded workers still get their reservation.
            effective_jobs = jobs if daemon_live else len(active_roots)
            production_pids = _descendants(rows, roots) - excluded
            all_production_pids.update(production_pids)
            this_reserve = effective_jobs * float(config.get("production_cores_per_job", 2))
            reserved += this_reserve
            status_rows.append({
                "path": path, "phase": status.get("phase"),
                "status_age_seconds": max(0, current["epoch"] - float(status.get("epoch", 0))),
                "daemon_live": daemon_live, "reported_jobs": jobs,
                "reserved_jobs": effective_jobs, "reserved_cpu_cores": this_reserve,
                "live_processes": len(production_pids),
            })
        except (OSError, ValueError, TypeError, KeyError) as error:
            blocked = True
            status_rows.append({"path": path, "error": repr(error)})
    measured = sum(cpu.get(pid, 0.0) for pid in all_production_pids)
    return reserved, measured, status_rows, blocked


def _limits(*, external_cpu, production_cpu, production_reserved,
            cpu_cap, memory_available, owned_rss, memory_reserve,
            worker_memory, max_workers, owned_workers,
            memory_admission_mode="fixed_worker_allowance",
            incremental_worker_memory=GIB, memory_admission_floor=10 * GIB,
            startup_debt=0):
    other_cpu = max(0.0, external_cpu - production_cpu)
    accounted_external = other_cpu + max(production_cpu, production_reserved)
    cpu_limit = max(0, math.floor(cpu_cap - accounted_external + 1e-9))
    if memory_admission_mode == "fixed_worker_allowance":
        # Preserve the original ceiling-reservation policy by default.
        memory_limit = max(0, math.floor(
            (memory_available + owned_rss - memory_reserve) / worker_memory))
    elif memory_admission_mode == "actual_rss_incremental":
        if incremental_worker_memory <= 0 or startup_debt < 0 or memory_admission_floor < 0:
            raise ValueError("Invalid incremental memory allowance, floor, or startup debt")
        available_for_new = max(0, memory_available - max(memory_reserve, memory_admission_floor) - startup_debt)
        memory_limit = owned_workers + available_for_new // incremental_worker_memory
    else:
        raise ValueError("Unknown memory_admission_mode: " + str(memory_admission_mode))
    limit = max(0, min(max_workers, cpu_limit, memory_limit))
    return {
        "worker_limit": limit,
        "dispatch_slots": max(0, limit - owned_workers),
        "owned_workers": owned_workers,
        "over_limit_running_workers": max(0, owned_workers - limit),
        "cpu_worker_limit": cpu_limit,
        "memory_worker_limit": memory_limit,
        "other_external_cpu_cores": other_cpu,
        "accounted_external_cpu_cores": accounted_external,
        "accounted_cpu_cores_with_current_workers": accounted_external + owned_workers,
        "accounted_cpu_cores_at_limit": accounted_external + limit,
        "action_if_over_limit": "KEEP_RUNNING_WORKERS; PAUSE_NEW_DISPATCH",
    }


def capacity_sample(root, owned_pids, config=None):
    """Return admission limits and save a bounded persistent CPU delta sample.

    owned_pids contains live worker PID roots, not the supervisor's PID.
    This function must run on X/Linux. It creates no tasks or subprocesses.
    Any resource/status read error raises or blocks admission; the caller should
    preserve its workers and record the exception rather than assume capacity.
    """
    config = dict(config or {})
    if not Path("/proc/self/stat").is_file():
        raise RuntimeError("capacity_sample requires Linux /proc on X")
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    state_path = root / "CAPACITY_STATE.json"
    try:
        previous = json.loads(state_path.read_text())
    except (OSError, ValueError):
        previous = None
    current = _snapshot()
    bootstrap = (
        not previous
        or previous.get("uptime_clock") != "CLOCK_BOOTTIME"
        or previous.get("boot_id") != current["boot_id"]
        or previous.get("ticks_per_second") != current["ticks_per_second"]
        or not 0.05 <= current["monotonic"] - previous.get("monotonic", 0) <= float(
            config.get("max_sample_gap_seconds", 30))
        or not isinstance(previous.get("rows"), dict)
    )
    if bootstrap:
        previous = current
        time.sleep(min(5.0, max(0.05, float(config.get("initial_sample_seconds", 0.25)))))
        current = _snapshot()
    cpu, sample_seconds = _cpu_delta(previous, current)
    rows = current["rows"]
    own_roots = {
        str(int(pid)) for pid in owned_pids
        if str(int(pid)) in rows and rows[str(int(pid))]["state"] not in ("Z", "X")
        and int(pid) != os.getpid()
    }
    owned = _descendants(rows, own_roots)
    excluded = owned | {str(os.getpid())}
    external = sum(value for pid, value in cpu.items() if pid not in excluded)
    own_cpu = sum(cpu.get(pid, 0.0) for pid in owned)
    own_rss = sum(rows[pid]["rss"] for pid in owned)
    reserve, prod_cpu, status_rows, status_error = _production_reservation(
        current, cpu, excluded, config)
    memory_available, memory_total = _read_memory()
    affinity = len(os.sched_getaffinity(0))
    cpu_cap = min(affinity, max(0, float(config.get("total_cpu_cap", 44))))
    memory_reserve = int(float(config.get("memory_reserve_gib", 8)) * GIB)
    worker_memory = int(float(config.get("worker_memory_gib", 4)) * GIB)
    if worker_memory <= 0 or memory_reserve < 0:
        raise ValueError("Invalid worker memory allowance or reserve")
    memory_mode = config.get("memory_admission_mode", "fixed_worker_allowance")
    incremental_memory = int(float(config.get("incremental_worker_gib", 1)) * GIB)
    admission_floor = int(float(config.get("memory_admission_floor_gib", 10)) * GIB)
    startup_seconds = float(config.get("memory_startup_seconds", 60))
    if (incremental_memory <= 0 or admission_floor < 0 or
            not math.isfinite(startup_seconds) or startup_seconds < 0):
        raise ValueError("Invalid incremental memory policy")
    memory_groups, startup_debt = _owned_memory_groups(
        current, own_roots, incremental_memory, startup_seconds)
    result = _limits(
        external_cpu=external, production_cpu=prod_cpu, production_reserved=reserve,
        cpu_cap=cpu_cap, memory_available=memory_available, owned_rss=own_rss,
        memory_reserve=memory_reserve, worker_memory=worker_memory,
        max_workers=max(0, int(config.get("max_workers", 40))), owned_workers=len(own_roots),
        memory_admission_mode=memory_mode, incremental_worker_memory=incremental_memory,
        memory_admission_floor=admission_floor, startup_debt=startup_debt)
    warnings = []
    if current["permission_denied"] or previous.get("permission_denied"):
        warnings.append("Not all process CPU statistics readable; new dispatch blocked")
    if status_error:
        warnings.append("A required production status could not be read; new dispatch blocked")
    if warnings:
        result.update(worker_limit=0, dispatch_slots=0,
                      over_limit_running_workers=len(own_roots),
                      accounted_cpu_cores_at_limit=result["accounted_external_cpu_cores"])
    result.update({
        "epoch": current["epoch"], "sample_seconds": sample_seconds,
        "uptime_clock": current["uptime_clock"],
        "bootstrap_sample": bootstrap, "affinity_cpu_count": affinity,
        "total_cpu_cap": cpu_cap, "configured_max_workers": int(config.get("max_workers", 40)),
        "external_cpu_cores": external, "owned_measured_cpu_cores": own_cpu,
        "production_cpu_cores": prod_cpu, "production_reserved": reserve,
        "production_status": status_rows,
        "memory_available": memory_available,
        "memory_available_bytes": memory_available, "memory_total_bytes": memory_total,
        "memory_reserve_bytes": memory_reserve, "owned_rss_bytes": own_rss,
        "worker_memory_bytes": worker_memory,
        "memory_admission_mode": memory_mode,
        "memory_admission_floor_bytes": admission_floor,
        "memory_effective_admission_floor_bytes": max(memory_reserve, admission_floor)
            if memory_mode == "actual_rss_incremental" else memory_reserve,
        "incremental_worker_memory_bytes": incremental_memory,
        "memory_startup_seconds": startup_seconds,
        "memory_startup_debt_bytes": startup_debt if memory_mode == "actual_rss_incremental" else 0,
        "owned_memory_groups": memory_groups,
        "memory_pressure_guard_required": memory_mode == "actual_rss_incremental",
        "memory_policy": "MemAvailable already excludes current resident memory; reserve only new groups and young-group startup debt"
            if memory_mode == "actual_rss_incremental" else "Reserve worker_memory_bytes for every owned worker after adding back owned RSS",
        "owned_pids": sorted(map(int, own_roots)),
        "cpu_measurement": "live_process_utime_plus_stime_delta; owned_and_supervisor_excluded",
        "cpu_measurement_caveat": "Processes that exit between samples may be missed; production gets per-job headroom",
        "warnings": warnings,
    })
    _atomic(state_path, current)
    return result


def apply_worker_limits(config=None):
    """Call once in a fresh worker BEFORE importing scientific libraries."""
    config = dict(config or {})
    for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                 "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        os.environ[name] = "1"
    os.environ["OMP_THREAD_LIMIT"] = "1"
    os.environ["HIGHS_THREADS"] = "1"
    desired = int(float(config.get("worker_memory_gib", 4)) * GIB)
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    effective = desired if hard == resource.RLIM_INFINITY else min(desired, hard)
    resource.setrlimit(resource.RLIMIT_AS, (effective, effective))
    priority = os.getpriority(os.PRIO_PROCESS, 0)
    if priority < 10:
        os.setpriority(os.PRIO_PROCESS, 0, 10)
    return {"rlimit_as_bytes": effective, "nice": os.getpriority(os.PRIO_PROCESS, 0),
            "library_threads": 1}


def self_test():
    """Pure accounting tests only; no /proc, CPU work, files, sleep, or limits."""
    common = dict(cpu_cap=44, memory_available=90 * GIB, owned_rss=0,
                  memory_reserve=8 * GIB, worker_memory=4 * GIB,
                  max_workers=40, owned_workers=0)
    # Six production jobs currently consume six cores. Reserve their possible
    # 12 exact-verifier cores, plus two genuinely unrelated measured cores.
    a = _limits(external_cpu=8, production_cpu=6, production_reserved=12, **common)
    assert a["accounted_external_cpu_cores"] == 14
    assert a["cpu_worker_limit"] == 30 and a["worker_limit"] == 20
    # Production's measured usage already exceeds reservation: do not add it.
    b = _limits(external_cpu=15, production_cpu=13, production_reserved=12, **common)
    assert b["accounted_external_cpu_cores"] == 15
    # A load spike closes admission without suggesting process termination.
    c = _limits(external_cpu=45, production_cpu=12, production_reserved=12,
                **dict(common, owned_workers=8))
    assert c["worker_limit"] == c["dispatch_slots"] == 0
    assert c["over_limit_running_workers"] == 8
    # Existing resident memory must be added back once, not once per sample.
    d = _limits(external_cpu=0, production_cpu=0, production_reserved=0,
                **dict(common, memory_available=70 * GIB, owned_rss=20 * GIB, owned_workers=10))
    assert d["worker_limit"] == 20 and d["dispatch_slots"] == 10
    rows = {"1": {"ppid": 0}, "2": {"ppid": 1}, "3": {"ppid": 2}, "4": {"ppid": 0}}
    assert _descendants(rows, [1]) == {"1", "2", "3"}
    hz = 100
    prev = {"monotonic": 10, "uptime": 100, "ticks_per_second": hz,
            "rows": {"1": {"start": 10, "ticks": 100}}}
    now = {"monotonic": 12, "ticks_per_second": hz,
           "rows": {"1": {"start": 10, "ticks": 300},
                    "2": {"start": 10100, "ticks": 50}}}
    delta, seconds = _cpu_delta(prev, now)
    assert seconds == 2 and delta == {"1": 1.0, "2": 0.25}
    return {"status": "PASS", "cases": 6, "math_replay_performed": False}


def incremental_self_test():
    """Budget-boundary and descendant-accounting checks; no I/O or processes."""
    common = dict(external_cpu=18, production_cpu=8, production_reserved=12,
                  cpu_cap=44, memory_available=52 * GIB, owned_rss=6 * GIB,
                  memory_reserve=8 * GIB, worker_memory=4 * GIB,
                  max_workers=40, owned_workers=15)
    dynamic = dict(common, memory_admission_mode="actual_rss_incremental")
    legacy = _limits(**common)
    released = _limits(**dynamic)
    # The observed workload is CPU-bound after removing unused ceiling reserves.
    assert legacy["memory_worker_limit"] == 12 and legacy["dispatch_slots"] == 0
    assert released["memory_worker_limit"] == 57
    assert released["worker_limit"] == 22 and released["dispatch_slots"] == 7
    assert released["accounted_cpu_cores_at_limit"] == 44
    # Existing RSS cannot be added back: otherwise one could spend it twice.
    changed_rss = _limits(**dict(dynamic, owned_rss=30 * GIB))
    assert changed_rss == released
    # Below the admission floor, keep existing groups but grant no new slot.
    low = _limits(**dict(dynamic, memory_available=9 * GIB))
    assert low["memory_worker_limit"] == 15 and low["dispatch_slots"] == 0
    edge = _limits(**dict(dynamic, memory_available=11 * GIB - 1))
    assert edge["dispatch_slots"] == 0
    exact = _limits(**dict(dynamic, memory_available=11 * GIB))
    assert exact["dispatch_slots"] == 1
    # Larger operator reserves win over the default admission floor.
    reserve = _limits(**dict(dynamic, memory_available=14 * GIB, memory_reserve=12 * GIB))
    assert reserve["dispatch_slots"] == 2
    # A new parent plus LP helper receives ONE combined startup allowance.
    now = {"uptime": 100, "ticks_per_second": 100, "rows": {
        "1": {"ppid": 0, "start": 9000, "rss": GIB // 4},
        "2": {"ppid": 1, "start": 9100, "rss": GIB // 2},
        "3": {"ppid": 0, "start": 4000, "rss": GIB // 8},
        "4": {"ppid": 0, "start": 9200, "rss": 10 * GIB},
    }}
    groups, debt = _owned_memory_groups(now, [1, 3], GIB, 60)
    assert debt == GIB // 4
    assert groups[0]["descendant_pids"] == [1, 2]
    assert groups[0]["group_rss_bytes"] == 3 * GIB // 4
    assert groups[1]["within_startup_window"] is False
    # Reserve that startup shortfall even when current RSS has not grown yet.
    paid_debt = _limits(**dict(dynamic, memory_available=12 * GIB, startup_debt=debt))
    assert paid_debt["dispatch_slots"] == 1
    no_room = _limits(**dict(dynamic, memory_available=11 * GIB, startup_debt=2 * GIB))
    assert no_room["memory_worker_limit"] == 15 and no_room["dispatch_slots"] == 0
    # CPU spikes still override plentiful memory; never terminate existing work.
    high_cpu = _limits(**dict(dynamic, external_cpu=50))
    assert high_cpu["dispatch_slots"] == 0 and high_cpu["worker_limit"] == 0
    # Overlapping roots do not count helper RSS twice or cancel another debt.
    nested, nested_debt = _owned_memory_groups(now, [1, 2], GIB, 60)
    assert sum(g["group_rss_bytes"] for g in nested) == 3 * GIB // 4
    assert nested_debt == 5 * GIB // 4
    return {"status": "PASS", "cases": 8, "math_replay_performed": False}


if __name__ == "__main__":
    print(json.dumps({"status": "PASS", "legacy": self_test(),
                      "incremental": incremental_self_test()}, sort_keys=True))
