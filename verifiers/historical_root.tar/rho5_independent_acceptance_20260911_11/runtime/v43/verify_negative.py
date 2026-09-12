import copy,json
from fractions import Fraction as Q
import local_guard as g
import box_budget as bb

def run():
    cert=json.loads((g.ROOT/'chart_certificate.json').read_text());passed=[]
    def rejects(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):passed.append(name);return
        raise ValueError('Bad input accepted: '+name)
    for name,edit in [
      ('radius',lambda c:c.update(radius='1/250')),('gain',lambda c:c.update(gain='1/8')),
      ('speed',lambda c:c.update(speed='2')),('schema',lambda c:c.update(schema='wrong')),
      ('missing_chart',lambda c:c['charts'].pop()),
      ('duplicate_chart',lambda c:c['charts'].__setitem__(1,copy.deepcopy(c['charts'][0]))),
      ('unknown_field',lambda c:c.update(trusted=True)),
      ('false_case_bool',lambda c:c['charts'][0].update(case=True)),
      ('wrong_released_band',lambda c:c['charts'][0]['active_labels'].__setitem__(0,'P0-')),
      ('corrupt_inverse',lambda c:c['charts'][0]['preconditioner'][0].__setitem__(0,'0')),
      ('float_matrix_entry',lambda c:c['charts'][0]['preconditioner'][0].__setitem__(0,0.5))]:
        bad=copy.deepcopy(cert);edit(bad);rejects(name,lambda bad=bad:g.verify_local(bad))
    z=json.loads((g.ROOT/'controls/boundary_controls.json').read_text())[0]['z'];case=0
    rejects('negative_loss',lambda:g.point_entry(z,'-1/100',case))
    rejects('float_loss',lambda:g.point_entry(z,0.0,case))
    rejects('wrong_dimension',lambda:g.point_entry(z[:-1],'0',case))
    zz=z[:];zz[19]=str(Q(zz[19])-Q(1,10**8))
    rejects('nonphysical_P0_input',lambda:g.point_entry(zz,'0',case))
    box=[[v,v]for v in z]
    rejects('reversed_interval',lambda:bb.x_budget([['1','0']]+box[1:],case))
    rejects('unknown_transport',lambda:bb.b_transport_budget(box,'0',case,'unproved'))
    # Full-budget equality is accepted, a strict excess is not; conditional arithmetic only.
    got=bb.b_transport_budget(box,'0',case,'R');d=got['distance_upper']
    eq=(g.RADIUS-d)/g.B_COSTS[case]
    g.need(bb.b_transport_budget(box,str(eq),case,'R')['status']=='CONDITIONAL_ALPHA_SAFE','closed entrance')
    g.need(bb.b_transport_budget(box,str(eq+Q(1,10**15)),case,'R')['status']=='OPEN','outside entrance')
    # A positive-width box straddling the P0 boundary remains eligible, but only
    # its complete physical subset is covered; automatic P0 positivity is false.
    eps=Q(1,10**10);fat=[[str(Q(v)-eps),str(Q(v)+eps)]for v in z]
    xb=bb.x_budget(fat,case)
    g.need(xb['status']=='CONDITIONAL_PHYSICAL_X_HEIGHT_BUDGET'and not xb['P0_automatically_positive_on_box'],'physical intersection, not all-point positivity')
    return dict(status='V43_NEGATIVE_AND_CLOSED_BOUNDARY_TESTS_PASS',rejected=len(passed),names=passed,closed_threshold_checks=2,positive_width_P0_crossing_box=xb)
if __name__=='__main__':print(json.dumps(g.jsonable(run()),indent=2))
