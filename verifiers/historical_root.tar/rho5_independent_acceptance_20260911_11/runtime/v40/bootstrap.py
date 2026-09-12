"""Mount the unmodified received LIGHT source package in an isolated directory.
No tree is present or downloaded. Never writes into a user's running campaign.
"""
from pathlib import Path, PurePosixPath
import tempfile,zipfile,sys,hashlib
ROOT=Path(__file__).resolve().parent
ARCHIVE=ROOT/'dependency'/'RHO5_ROUND49_V39_LIGHT.zip'
ARCHIVE_SHA=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()
_TMP=tempfile.TemporaryDirectory(prefix='rho5_v40_received_')
with zipfile.ZipFile(ARCHIVE)as z:
 for m in z.infolist():
  p=PurePosixPath(m.filename)
  if p.is_absolute()or'..'in p.parts:raise ValueError('Unsafe archive entry')
 z.extractall(_TMP.name)
RECEIVED=Path(_TMP.name)/'rho5_round49_v39'
V39=RECEIVED/'v39'
if str(V39)not in sys.path:sys.path.insert(0,str(V39))
