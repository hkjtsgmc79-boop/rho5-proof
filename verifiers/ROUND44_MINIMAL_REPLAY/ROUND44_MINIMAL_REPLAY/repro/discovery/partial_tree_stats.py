"""Read-only discovery diagnostics; never a proof acceptance decision."""
from pathlib import Path
import json, sys

for directory in map(Path,sys.argv[1:]):
    path=directory if directory.is_file() else directory/'result.tree'
    if not path.exists():
        continue
    pending=[0];leaves=0;nodes=0;mass=0.0
    with path.open() as f:
        for line in f:
            fields=line.split()
            if not fields or not pending:break
            if fields[0]=='S' and len(fields)==2:
                depth=pending.pop();pending.extend([depth+1,depth+1]);nodes+=1
            elif fields[0]=='C' and len(fields)>1 and len(fields)==2+2*int(fields[1]):
                depth=pending.pop();leaves+=1;nodes+=1;mass+=2.0**(-depth)
            else:break
    print(json.dumps(dict(directory=str(directory),complete_records=nodes,leaves=leaves,
        remaining_stack=len(pending),closed_root_volume_fraction=mass,
        shallowest_unpaid_depth=min(pending) if pending else None,
        diagnostic_only=True)))
