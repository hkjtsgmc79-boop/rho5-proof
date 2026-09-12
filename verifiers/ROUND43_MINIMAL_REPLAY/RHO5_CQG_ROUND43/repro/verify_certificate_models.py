"""Audit each frozen quadratic model against the analytic necessity formulas.

The separate C++ verifier proves emptiness of that frozen model root. This file
checks that its rows and root are sound consequences of the physical model.
Run on X; no optimizer, no numerical tolerance.
"""
from pathlib import Path
import argparse, json, re
import sympy as s
from build_large_model import model


def audit(directory):
    data=json.loads((directory/'model.json').read_text())
    vs,_,necessary,lo,hi,target=model(s.Rational(data['klo']),data['head_case'],True,root_grid=None)
    assert data['variables']==list(map(str,vs))
    assert s.Rational(data['target'])==target
    expected={name:poly.as_expr() for name,poly in necessary}
    names=[]
    for row in data['rows']:
        name=row['name'];names.append(name)
        assert name in expected,name
        poly=s.sympify(row['polynomial'],locals=dict(zip(map(str,vs),vs)))
        assert s.expand(poly-expected[name])==0,name
        multiplier=s.Rational(row.get('row_multiplier',data['base_multiplier']))
        assert multiplier>0
        terms=list(vs)+[vs[i]*vs[j] for i,j in data['pairs']]
        assert len(terms)==len(row['coefficients'])
        represented=row['rhs']-sum(a*b for a,b in zip(row['coefficients'],terms))
        assert s.expand(represented-multiplier*poly)==0,name
    assert len(names)==len(set(names))
    assert {'F','head_parabola','stage_parabola','core_parabola','common_head_loss'}<=set(names)
    den=data['root_denominator'];assert den>0
    actual_lo=[s.Rational(t,den) for t in data['root_numerators'][0]]
    actual_hi=[s.Rational(t,den) for t in data['root_numerators'][1]]
    for i in range(len(vs)):
        assert actual_lo[i]<=lo[i]<=hi[i]<=actual_hi[i],(str(vs[i]),actual_lo[i],lo[i],hi[i],actual_hi[i])
    header=(directory/'mc_exact_model.hpp').read_text()
    for label,value in [('EV',len(vs)),('EN',len(vs)+len(data['pairs'])),('EB',len(names)),
                        ('BASE_SCALE',data['base_multiplier']),('ROOT_DEN',den)]:
        assert re.search(r'\b'+label+r'='+str(value)+r'\b',header),label
    for label,value in [('epairs',data['pairs']),('ebase',[r['coefficients'] for r in data['rows']]),
                        ('erhs',[r['rhs'] for r in data['rows']]),
                        ('erootlo',data['root_numerators'][0]),('eroothi',data['root_numerators'][1])]:
        encoded=re.search(r'\b'+label+r'=(\{.*?\});',header).group(1)
        assert json.loads(encoded.replace('{','[').replace('}',']'))==value,label
    return dict(case=data['head_case'],K=data['klo'],rows=len(names),products=len(data['pairs']),
                root_covers_analytic_necessary_root=True,exact_header_matches_model=True)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('cases',nargs='+');a=ap.parse_args()
    rows=[audit(Path(d)) for d in a.cases]
    cases={r['case'] for r in rows}
    assert cases in ({'I','II'},{'I','II','III'})
    assert len({r['K'] for r in rows})==1
    print(json.dumps(dict(status='FROZEN_MODELS_NECESSITY_AUDIT_PASS',cases=rows,
                         III_coverage='Exact J M^T J plus head-preserving A normalization maps III to II.'),indent=2))


if __name__=='__main__':main()
