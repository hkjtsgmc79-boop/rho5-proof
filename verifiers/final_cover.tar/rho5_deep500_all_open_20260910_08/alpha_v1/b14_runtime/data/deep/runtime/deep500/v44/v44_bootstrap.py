"""Load the exact, byte-preserved U41 dependencies from this package."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
FROZEN=ROOT/'frozen/v41'
sys.path.insert(0,str(FROZEN))
import source_access as source
import dual_box as db
import v41_protocol as vp
for module in (source,db,vp):
 if Path(module.__file__).resolve().parent != FROZEN.resolve():
  raise ImportError('Unexpected dependency resolution: '+str(module.__file__))
sys.path.insert(0,str(ROOT))
fs=source.fs
Q=fs.Q
I=fs.I
