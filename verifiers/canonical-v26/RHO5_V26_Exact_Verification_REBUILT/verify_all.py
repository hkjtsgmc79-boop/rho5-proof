import subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
tests=[
    "verify_symbolic.py",
    "verify_guard_dictionary.py",
    "verify_p61_root.py",
    "verify_resultant.py",
]
for t in tests:
    print("==>", t)
    subprocess.run([sys.executable, str(HERE/t)], cwd=HERE, check=True)
print("V26_REBUILT_EXACT_CORE_PASSED")
