# Selective public-archive assembly preflight (30 September 2026)

This is an identity and entry-point check for the negative-diagonal finite-cover replay. It is **not** an execution of the 570 producer jobs, the original-root mathematical verifier, the entire upstream complete-X chain, or the full theorem.

On the fixed X Linux host, the two already cached public v1.0.0 archives were SHA-256 checked as complete compressed files:

| Public archive | Verified SHA-256 |
| --- | --- |
| `historical_root.tar.gz` | `15ef795e85d0d295e92fdd629f313b9c284cc6519388011862aee3c1e18e3f73` |
| `final_cover.tar.gz` | `1c9fb99d184eaf9d79b44d33826e4db8fbced8db41ee2b46ec2e1616bd12361c` |

The selected-member manifest in this directory identifies only the files needed for this preflight. A new, task-specific source directory was populated **from the compressed public archives**, not from the host's earlier extracted source trees. Extraction checked each selected member's SHA-256 and size: four members (2,102,875,884 bytes) from `historical_root.tar.gz` and 702 members (627,425,250 bytes) from `final_cover.tar.gz`. Disk space did not permit a second full extraction of both archives, so this result is **selective clean assembly**, not a full-archive cold replay.

Using those selected inputs, the unmodified `prepare_remote.py` and `replay_parents.py plan` completed in an isolated workspace. The generated plan has 570 jobs, 566 targets and 483 pinned files. A structural comparison of `FRESH_EXECUTABLE_DEPENDENCY_MANIFEST.json` with the sealed executed manifest found one difference only: the newly generated `created_epoch`. No mathematical producer was executed in this preflight.

The files here preserve the selected member list, extraction result, path map, plan summary and generated dependency manifest. Historical absolute paths describe the X run; readers may choose their own directory for a new full extraction. The dated exact replay result and its limits are documented separately in [the replay guide](../../docs/REPLAY_20260930.md).
