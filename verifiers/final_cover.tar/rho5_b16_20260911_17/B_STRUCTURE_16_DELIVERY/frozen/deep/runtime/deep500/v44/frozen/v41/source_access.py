"""Read-only, hash-bound access to the supplied Round50 LIGHT source.
The full original tree is not present. No user's working directory is touched.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, sys, tempfile, zipfile
ROOT = Path(__file__).resolve().parent
IDENTITY = json.loads((ROOT/'dependency/IDENTITY.json').read_text())
ARCHIVE = ROOT/'dependency/RHO5_ROUND50_V40_LIGHT.zip'
if hashlib.sha256(ARCHIVE.read_bytes()).hexdigest() != IDENTITY['received_zip_sha256']:
    raise ValueError('Round50 LIGHT bytes do not match')
_TEMP = tempfile.TemporaryDirectory(prefix='rho5_v41_received_')
with zipfile.ZipFile(ARCHIVE) as z:
    for info in z.infolist():
        p = PurePosixPath(info.filename)
        if p.is_absolute() or '..' in p.parts:
            raise ValueError('Unsafe archive path')
    z.extractall(_TEMP.name)
SOURCE = Path(_TEMP.name)/'rho5_round50_v40'
sys.path.insert(0, str(SOURCE/'v40'))
import protocol as inherited
import full_source as fs
import ablation as inherited_ablation
from linear_certificate import dual_margin as inherited_margin
if hashlib.sha256((SOURCE/'models/B17_FULL.json').read_bytes()).hexdigest() != IDENTITY['b17_model_sha256']:
    raise ValueError('Unexpected B17 model')
if inherited.MODEL_SHA != IDENTITY['b17_model_sha256']:
    raise ValueError('Nested mathematical source has a different B17 model')
if json.loads((SOURCE/'models/B24_BASE.json').read_text()) != fs.BASE:
    raise ValueError('Nested source and Round50 actual image model differ')
