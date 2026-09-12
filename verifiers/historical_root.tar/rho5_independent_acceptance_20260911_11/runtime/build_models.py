#!/usr/bin/env python3
"""Freeze two ALTERNATIVE, compatible research interfaces.
B17: global frame projection; base source applied only to canonical image.
B18: 18 full-state tail-contact roots; never assert those contacts on a
prefix-renormalized image (the providers may change when p increases).
"""
from pathlib import Path
from itertools import product
import json,hashlib,tempfile,zipfile,importlib.util
from capacity import FRAME_NAMES
from interval_capacity import root_box,GAMMA
from symmetry import contact_orbits
ROOT=Path(__file__).parent

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,obj):
    text=json.dumps(obj,ensure_ascii=False,sort_keys=True,indent=2)+'\n';Path(path).write_text(text);return hashlib.sha256(text.encode()).hexdigest()
def generate():
    out=ROOT/'models';out.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory()as tmp:
        with zipfile.ZipFile(ROOT/'dependency/rho5_v36_exact.zip')as z:z.extractall(tmp)
        source=Path(tmp)/'rho5_v36_exact/build_b_models.py'
        spec=importlib.util.spec_from_file_location('frozen_v36_model_builder',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        base=m.payload()
    basehash=write(out/'B24_BASE.json',base)
    root={'schema':'V37_CANONICAL_FRAME_ROOT_V1','frame_order':list(FRAME_NAMES),'bounds':dict(zip(FRAME_NAMES,[i.data()for i in root_box()])),
      'gamma':str(GAMMA),'target':'exact_alpha','alpha_file_sha256':sha(ROOT/'dependency/alpha.json'),
      'V36_flow_certificate_sha256':sha(ROOT/'dependency/two_gap_certificate.json'),
      'base_model_sha256':basehash,'source_scope':'same complete real normalized negative D; any hypothetical F>alpha is mapped by the explicit three-leg path',
      'normalization':'e,beta>0 from F>4; x0>=0 and A<=0 via actual sign congruences',
      'branch_coordinates':17,'eliminated_actual_coordinates':['beta','p','e','r','s','t'],
      'low_order_frozen_inputs':['real rho3=9/4','real rho4=4','head determinant pk<=4'],
      'no_tail_contact_equations_on_canonical_image':True,'status':'OPEN','macro_ledger':'14/15'}
    rh=write(out/'B17_FULL.json',root)
    reps=[]
    for i,(labels,parents)in enumerate(sorted(contact_orbits().items())):
        rows=dict(base['rows_ge_zero'])
        for l in labels:rows['eq_reverse_'+l]=[{'monomial':term['monomial'],'coefficient':str(-m.Q(term['coefficient']))}for term in rows[l]]
        model={**base,'schema':'V37_B18_ACTUAL_CONTACT_ROOT_V1','id':f'B18_{i:02d}','parent_model_sha256':basehash,
         'contact_equalities':list(labels),'rows_ge_zero':rows,'old_label_preimages':parents,
         'capacity_oracle_scope':'independent alpha upper bound for this source frame; do NOT append current source contact equalities to its canonical image',
         'status':'OPEN','macro_ledger':'14/15'}
        h=write(out/(model['id']+'.json'),model);reps.append({'id':model['id'],'sha256':h,'contacts':list(labels)})
    return {'B17_root_sha256':rh,'B24_base_sha256':basehash,'B18_count':len(reps),'representatives':reps}
if __name__=='__main__':
    ans=generate();write(ROOT/'models/ROOT_MANIFEST.json',ans);print(json.dumps({'status':'V37_MODELS_FROZEN_NOT_SOLVED','frame_variables':17,'actual_contact_roots':18}))

# The partition below is an exact work allocation, NOT 40 proven regions.
def partition40():
    from tree_protocol import digest,MODEL,halve
    from interval_capacity import root_box
    roots=root_box();widths=[v.hi-v.lo for v in roots]
    leaves=[('',roots,[])];splits={}
    while len(leaves)<40:
        # Breadth first, with normalized longest-side splitting.
        n=min(range(len(leaves)),key=lambda i:(len(leaves[i][0]),leaves[i][0]))
        path,box,route=leaves.pop(n)
        axis=max(range(17),key=lambda j:(box[j].hi-box[j].lo)/widths[j]);splits[path]=axis
        for child,b in enumerate(halve(box,axis)):
            leaves.append((path+str(child),b,route+[{'axis':axis,'child':child}]))
    leaves.sort()
    data={'model_sha256':digest(MODEL),'splits':splits,'leaves':[{'task':i,'path':path,'route':route,'box':[x.data()for x in box]}for i,(path,box,route)in enumerate(leaves)],'status':'PARTITION_ONLY_ALL_TASKS_OPEN'}
    (ROOT/'models/PARTITION40.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':partition40()
