"""Optional symbolic regeneration; NOT needed for default exact acceptance."""
import argparse,json
from fractions import Fraction as Q
import local_guard as g

def generate():
    import sympy as s
    b3,_,_=g.source();lm=b3.lm;pol=lm.source();cols=[i for i,n in enumerate(lm.NAMES)if n!='p'];charts=[]
    for case,sw in [(0,False),(0,True),(1,False),(2,False),(2,True),(3,False)]:
        center,active,_=g.chart_data(case,sw)
        entries=[[lm.ev(lm.diff(pol[label],i),center)for i in cols]for label in active]
        M=s.Matrix([[s.Rational(v.numerator,v.denominator)for v in row]for row in entries]);C=M.inv()
        charts.append(dict(case=case,swapped=sw,active_labels=active,
          preconditioner=[[str(Q(int(C[i,j].p),int(C[i,j].q)))for j in range(21)]for i in range(21)]))
    obj=dict(schema='V43_P0_GUARD_PRESERVING_CHARTS_V1',radius=str(g.RADIUS),gain=str(g.GAIN),speed=str(g.SPEED),charts=charts)
    g.verify_local(obj);return obj
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);a=ap.parse_args()
    from pathlib import Path
    p=Path(a.output)
    if p.exists():raise SystemExit('Refusing to overwrite an existing certificate; choose a fresh output.')
    p.write_text(json.dumps(generate(),indent=2)+'\n')
