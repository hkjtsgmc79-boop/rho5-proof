from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
FROZEN=ROOT/'dependency'/'round48'
if str(FROZEN) not in sys.path: sys.path.insert(0,str(FROZEN))
