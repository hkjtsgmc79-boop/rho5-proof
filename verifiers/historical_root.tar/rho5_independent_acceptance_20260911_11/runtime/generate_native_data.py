#!/usr/bin/env python3
"""Generate only frozen B17 data; no equations or contact constraints are added."""
from pathlib import Path
import hashlib, json
from fractions import Fraction

ROOT = Path(__file__).resolve().parent
FILES = ('models/B17_FULL.json', 'models/B24_BASE.json', 'dependency/alpha.json', 'dependency/two_gap_certificate.json')

def generate(output=None):
    docs = {name: json.loads((ROOT/name).read_text()) for name in FILES}
    ids = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in FILES}
    frame, base, alpha, cert = (docs[name] for name in FILES)
    assert ids[FILES[0]] == '39a65f2cbd6089dab3a403c6a72f365a02003737a641be86c3cf73cb70e76de3'
    assert frame['base_model_sha256'] == ids[FILES[1]]
    assert frame['alpha_file_sha256'] == ids[FILES[2]]
    assert frame['V36_flow_certificate_sha256'] == ids[FILES[3]]
    assert len(base['rows_ge_zero']) == 106 and frame['no_tail_contact_equations_on_canonical_image']
    expected_gap = ['k','r','w','A','B','c','d','p','e','beta'] + [f'{a}{i}' for a in ('u','x','v','q') for i in range(3)] + ['sigma','tau']
    assert cert['coordinate_order'] == expected_gap
    exact=lambda value:str(Fraction(value))
    rows=[[{'coefficient':exact(term['coefficient']),'monomial':term['monomial']}for term in row]
          for row in base['rows_ge_zero'].values()]
    data = {'identities': ids, 'root': [[exact(x)for x in frame['bounds'][name]] for name in frame['frame_order']],
            'gamma': exact(frame['gamma']), 'alpha_lower': exact(alpha['isolating_interval']['lower']),
            'coordinates': base['coordinate_order'], 'rows': rows,
            'centers': [[exact(x)for x in case['center']] for case in cert['cases']]}
    literal = json.dumps(data, separators=(',', ':'))
    assert ')B17DATA"' not in literal
    target = Path(output) if output is not None else ROOT/'b17_native_data.hpp'
    target.write_text('#pragma once\nstatic const char B17_DATA[] = R"B17DATA('+literal+')B17DATA";\n')
    return {'header_sha256': hashlib.sha256(target.read_bytes()).hexdigest(), 'identities': ids}

if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
