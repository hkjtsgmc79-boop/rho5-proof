"""Independent new dictionaries, B envelope, flow guard and negative controls.
No B global original-root tree is generated or accepted here.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import copy,hashlib,json,random,time
import sympy as sp
from gap_model import NAMES,source,check_actual,height,physical_matrix,ev
from b_tail_envelope import maximize_tail,interpolation
from build_b_models import NAMES as BN,source as b_source,payload,evaluate
from b_symmetry import normalized_transpose
from b_safe_ports import flow_cases,negative_d_box_to_gap_box
from verify_two_gap_certificate import verify as verify_flow
ROOT=Path(__file__).parent

def main():
    start=time.monotonic();nz=0
    def zero(x):
        nonlocal nz
        assert sp.cancel(x)==0,x;nz+=1
    v=sp.symbols(' '.join(NAMES));d=dict(zip(NAMES,v))
    k,r,w,A,B,c,h,p,e,be=v[:10];u=v[10:13];x=v[13:16];vv=v[16:19];q=v[19:22];sg,tg=v[22:24]
    D=sp.Matrix([[k,A,B],[c*k,r+c*A,r-sg+c*B],[h*k,r-tg+h*A,w+h*B]])
    S=D+sp.Matrix(x)*sp.Matrix(q).T;O=S+sp.Matrix(u)*sp.Matrix(vv).T
    M=sp.Matrix([[1,-e,*vv],[be,p-e*be,*[q[j]+be*vv[j] for j in range(3)]],
                 *[[u[i],p*x[i]-e*u[i],*list(O.row(i))] for i in range(3)]])
    S1=M[1:,1:]-M[1:,0:1]*M[0:1,1:]
    S2=S1[1:,1:]-S1[1:,0:1]*S1[0:1,1:]/p
    for a in S2-D:zero(a)
    H=D[1:,1:]-D[1:,0:1]*D[0:1,1:]/k
    for a in H-sp.Matrix([[r,r-sg],[r-tg,w]]):zero(a)
    F=(r-sg)*(r-tg)/r-w
    zero(H[1,1]-H[1,0]*H[0,1]/H[0,0]+F)
    zero(F-(r-w-sg-tg+sg*tg/r))
    independent={}
    def band(a,cap,label):
        for sign,tag in [(-1,'+'),(1,'-')]:
            ex=sp.expand(cap+sign*a)
            if ex!=0:independent[label+tag]=ex
    band(e,1,'e');band(be,1,'beta');band(p-e*be,1,'head')
    for i in range(3):
        for a,cap,label in [(u[i],1,'u'),(x[i],1,'x'),(vv[i],1,'v'),(q[i],p,'q')]:band(a,cap,label+str(i))
        band(p*x[i]-e*u[i],1,'L'+str(i));band(q[i]+be*vv[i],1,'P'+str(i))
        for j in range(3):
            for mat,cap,label in [(D,k,'D'),(S,p,'S'),(O,1,'O')]:band(mat[i,j],cap,label+str(i)+str(j))
    independent.update({'r+w':r+w,'r-w':r-w,'positive_p':p,'positive_k':k,'positive_r':r,
                        'sigma':sg,'tau':tg,'positive_s':r-sg,'positive_t':r-tg})
    rows=source();assert set(independent)==set(rows)
    def expr(poly,vars):
        return sum((sp.Rational(coef.numerator,coef.denominator)*sp.prod(vars[i] for i in mon) for mon,coef in poly.items()),sp.Integer(0))
    for n,g in rows.items():zero(expr(g,v)-independent[n])
    # Every full negative-D physical row equals the same native source under substitution.
    bv=sp.symbols(' '.join(BN));bd=dict(zip(BN,bv));sub={d[n]:bd[n] for n in NAMES if n in bd}
    sub.update({w:-bd['r'],sg:bd['r']-bd['s'],tg:bd['r']-bd['t']})
    br=b_source();phys=set(rows)-{'r+w','r-w','positive_p','positive_k','positive_r','sigma','tau','positive_s','positive_t'}
    for n in phys:zero(expr(br[n],bv)-independent[n].subs(sub,simultaneous=True))
    zero(expr(br['height_eq+'],bv)-(bd['r']*bd['F']-bd['r']**2-bd['s']*bd['t']))
    zero(expr(br['height_eq+'],bv)+expr(br['height_eq-'],bv))
    # Full monotone gain identity, exact and without guessed signs.
    rr,ss,tt,RR,SS,TT=sp.symbols('rr ss tt RR SS TT')
    zero(RR*rr*((RR+SS*TT/RR)-(rr+ss*tt/rr))-
         ((RR-rr)*(RR*rr-ss*tt)+rr*tt*(SS-ss)+rr*SS*(TT-tt)))
    # Derivative identity underlying the two-gap gain bound, with exact gap directions.
    velocity=sp.symbols('V0:24');generic=sum(sp.diff(F,v[i])*velocity[i] for i in range(24))
    for which,other in [(22,23),(23,22)]:
        target=velocity[1]-velocity[2]-1+v[other]/r-sg*tg*velocity[1]/r**2
        zero(generic.subs({velocity[22]:int(which==22),velocity[23]:int(which==23)})-target)
    # Generated frozen mathematical task models match the generator byte semantics.
    base_path=ROOT/'next_B_models/base_model.json';base=json.loads(base_path.read_text());assert base==payload()
    carrier=json.loads((ROOT/'next_B_models/contacts54.json').read_text());basehash=hashlib.sha256(base_path.read_bytes()).hexdigest()
    assert carrier['count']==54 and carrier['base_model_sha256']==basehash
    assert len({tuple(x['additional_equal_zero'])for x in carrier['models']})==54
    for t in carrier['models']:
        assert t['base_model_sha256']==basehash and len(t['additional_equal_zero'])==3
        assert all(n in br for n in t['additional_equal_zero']) and t['status']=='OPEN'
    # Four proper-B >gamma controls, full source and maximum-tail representatives.
    reps=json.loads((ROOT/'next_B_models/representatives36.json').read_text())
    assert reps['count']==36 and len(reps['models'])==36 and reps['base_model_sha256']==basehash
    expected_reps={t['id']for t in carrier['models']if 'DSO'.index(t['additional_equal_zero'][1][0])<='DSO'.index(t['additional_equal_zero'][2][0])}
    assert expected_reps=={t['id']for t in reps['models']}
    controls=json.loads((ROOT/'evidence/proper_B_controls.json').read_text())['controls']
    cert=json.loads((ROOT/'two_gap_certificate.json').read_text());point_checks=0;contact_matches=[]
    def bcoords(z):
        vals=dict(zip(NAMES,z));vals.update(s=z[1]-z[22],t=z[1]-z[23],F=height(z))
        return [vals[n]for n in BN]
    def check_model(z,check_root=True):
        zb=bcoords(z)
        for n,g in br.items():
            if n=='F_trigger' and not check_root:continue
            assert evaluate(g,zb)>=0,(n,str(evaluate(g,zb)))
        if check_root:
            for n,x0 in zip(BN,zb):
                lo,hi=map(Q,base['bounds'][n]);assert lo<=x0<=hi,n
        return zb
    for rec in controls:
        z=list(map(Q,rec['parameters']));check_actual(z);zb=check_model(z)
        assert rec['case'] in flow_cases([(a,a)for a in z],cert)
        affine=negative_d_box_to_gap_box([(a,a)for a in zb]);assert affine==[(a,a)for a in z]
        end=maximize_tail(z);check_actual(end['point']);ee=check_model(end['point'])
        matched=[t['id']for t in carrier['models']if all(evaluate(br[n],ee)==0 for n in t['additional_equal_zero'])]
        assert matched or end['paid_face'];contact_matches.append(matched);point_checks+=2
        trans=normalized_transpose(end['point']);transb=check_model(trans)
        m1={t['id']for t in carrier['models']if all(evaluate(br[n],ee)==0 for n in t['additional_equal_zero'])}
        m2={t['id']for t in carrier['models']if all(evaluate(br[n],transb)==0 for n in t['additional_equal_zero'])}
        assert (m1|m2)&expected_reps or end['paid_face']
        back=normalized_transpose(trans);assert back==end['point']
        point_checks+=2
    # 80 independent rational low-height complete fibres; closed/zero-arm cases included.
    rng=random.Random(360081);regressions=0;paths=0;paid=0;proper=0
    for it in range(80):
        z=[Q(0)]*24;z[0]=Q(1,4);z[1]=Q(1,8);z[2]=-z[1];z[7]=Q(3,4)
        z[3]=Q(-rng.randrange(0,16),400);z[4]=Q(rng.randrange(-15,16),400)
        z[5]=Q(rng.randrange(-15,16),100);z[6]=Q(rng.randrange(-15,16),100)
        for j in range(8,22):z[j]=Q(rng.randrange(-4,5),100)
        z[22]=Q(rng.randrange(0,5),40);z[23]=Q(rng.randrange(0,5),40)
        assert 0<=z[22]<=z[1] and 0<=z[23]<=z[1]
        check_actual(z);end=maximize_tail(z);check_actual(end['point']);check_model(z,False);check_model(end['point'],False)
        paid+=int(end['paid_face']);proper+=int(not end['paid_face']);regressions+=1
        for th in (Q(0),Q(1,3),Q(2,3),Q(1)):interpolation(z,th);paths+=1
    # Safe port strict boundary and input rejection, exact rationals only.
    rejected=[];boundary_checks=0
    for case in cert['cases']:
        c0=list(map(Q,case['center']))
        for shift,accept in [(Q(0),True),(Q(1,1250)-Q(1,10**12),True),(Q(1,1250),False),(Q(1,1250)+Q(1,10**12),False)]:
            z=c0[:];z[7]+=shift;got=case['case'] in flow_cases([(a,a)for a in z],cert);assert got==accept;boundary_checks+=1
        # Entire small closed box with positive gap widths is inside the flow tube.
        b=[(v-Q(1,10000),v+Q(1,10000))for v in c0];b[22]=b[23]=(Q(0),Q(1,10000))
        assert case['case'] in flow_cases(b,cert);boundary_checks+=1
    good=[(Q(0),Q(0))]*24
    for label,box in [('float',[(0.0,0.0)]+good[1:]),('bool',[(False,True)]+good[1:]),('reversed',[(Q(1),Q(0))]+good[1:]),('dimension',good[:-1])]:
        try:flow_cases(box,cert)
        except (AssertionError,ValueError,TypeError):rejected.append(label)
        else:raise AssertionError('malformed box accepted '+label)
    # Certificate tampering must fail its mathematical checks, not just a hash.
    changes=[('zero_preconditioner',lambda c:c['cases'][0].update(preconditioner=[['0']*23 for _ in range(23)])),
      ('duplicate_active',lambda c:c['cases'][0]['active_labels'].__setitem__(0,c['cases'][0]['active_labels'][1])),
      ('wrong_radius',lambda c:c.update(outer_radius='1/100')),
      ('wrong_gain',lambda c:c.update(gain='1/5')),
      ('wrong_coordinate',lambda c:c['coordinate_order'].__setitem__(0,'fake_k')),
      ('wrong_center',lambda c:c['cases'][0]['center'].__setitem__(8,'2'))]
    for label,change in changes:
        bad=copy.deepcopy(cert);change(bad)
        try:verify_flow(bad)
        except (AssertionError,ValueError,TypeError,KeyError):rejected.append(label)
        else:raise AssertionError('bad theorem certificate accepted '+label)
    out={'status':'V36_NEW_B_SOURCE_ENVELOPE_PORT_AND_MODEL_CHECKS_PASS','exact_symbolic_zero_assertions':nz,
         'gap_model_physical_rows':len(rows),'negative_D_physical_rows_compared':len(phys),'next_B_base_rows':len(br),
         'next_B_contact_models':54,'next_B_task_representatives':36,'proper_B_control_model_checks':point_checks,'control_contact_matches':contact_matches,
         'low_height_rational_fibres':regressions,'extra_tail_path_matrices':paths,
         'envelope_endpoints_on_paid_face':paid,'envelope_endpoints_still_proper':proper,
         'exact_safe_port_boundary_checks':boundary_checks,'bad_inputs_and_certificates_rejected':rejected,
         'global_B_original_root_tree_exists':False,'seconds':time.monotonic()-start}
    (ROOT/'evidence/new_components.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
