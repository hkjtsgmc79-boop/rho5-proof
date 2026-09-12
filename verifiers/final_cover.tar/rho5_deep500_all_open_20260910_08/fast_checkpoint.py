"""Same JSON bytes and commit protocol as discovery.atomic_json, one encoding.

Checkpoint frequency is unchanged. No batching, delayed flush, background writer,
format change, or mathematical rule change is introduced.
"""
from pathlib import Path
import json
import os
import tempfile


def atomic_json(path, data, max_bytes=None):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    # dump() streams through Python's recursive encoder. dumps() uses the C
    # encoder with the same options; real certificate byte equality is gated.
    payload = json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n'
    if max_bytes is not None and len(payload) > max_bytes:
        raise ValueError('CHECKPOINT_TOO_LARGE')
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name + '.', suffix='.tmp')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
