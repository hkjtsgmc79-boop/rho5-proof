"""Exact dual-certified box contraction. No optimizer is imported here.
All bounds in a wave use the same frozen relaxation before intersection.
Rebuilding a canonical enclosure is justified only for the same B17 maximum image.
"""
from source_access import fs, inherited, inherited_ablation
from pivot_windows import WINDOW_ROWS, cycle_rows
Q,I=fs.Q,fs.I
PROFILES=('BASE','PIVOT','CYCLE','PIVOT_CYCLE')

def validate_profile(profile):
    if profile not in PROFILES:raise ValueError('Unknown row profile')

def common_contract(parent, label=None, profile='BASE'):
    validate_profile(profile)
    if label is None:
        out=parent if parent['status']=='EMPTY' else inherited_ablation.baseline_contract(parent)
    else:
        if label not in fs.GRAPH_LABELS:raise ValueError('Unknown conditional chart')
        out=fs.contract_full(parent,label)
    if out['status']=='EMPTY':return out
    b=[I(*z) for z in out['aux_image']]
    rows=(fs.CHARTS[label][0] if label else [])+fs.BASE_POLYS+(WINDOW_ROWS if profile in ('PIVOT','PIVOT_CYCLE') else [])
    try:
      for iteration in range(8):
        prev=[z.data() for z in b]
        fs.propagate(b,rows)
        if label:fs.direct_bounds(b,label)
        fs.reconstruct_tail(b)
        h=fs.high_contract(b,rounds=2)
        if h['status']=='EMPTY':raise fs.Empty(h['reason'])
        for i,z in enumerate(h['aux_image']):fs.meet(b,i,Q(z[0]),Q(z[1]))
        if label:
            reason=fs.strict_impossible(label,b)
            if reason:raise fs.Empty(reason)
        if prev==[z.data() for z in b]:break
      return {'status':'BOUNDED','aux_image':[z.data() for z in b]}
    except fs.Empty as err:return {'status':'EMPTY','reason':str(err)}

def rows_and_bounds(aux,label=None,profile='BASE'):
    validate_profile(profile)
    polynomials=fs.BASE_POLYS+(fs.CHARTS[label][0] if label else [])+(WINDOW_ROWS if profile in ('PIVOT','PIVOT_CYCLE') else [])
    pairs=sorted({m for _,p in polynomials for m in p if len(m)==2})
    if any(len(m)>2 for _,p in polynomials for m in p):raise ValueError('Expected quadratic source')
    columns={m:24+i for i,m in enumerate(pairs)}
    boxes=[I(*z) for z in aux];rows=[]
    def append(polys):
      for name,p in polys:
        a={};rhs=p.get((),Q(0))
        for m,c in p.items():
          if not m:continue
          j=m[0] if len(m)==1 else columns[m]
          a[j]=a.get(j,Q(0))-c
        rows.append((a,rhs))
    append(polynomials)
    for (i,j),col in columns.items():
      li,ui=boxes[i].lo,boxes[i].hi;lj,uj=boxes[j].lo,boxes[j].hi
      for ai,aj,az,bb in ((lj,li,-1,li*lj),(uj,ui,-1,ui*uj),(-uj,-li,1,-li*uj),(-lj,-ui,1,-ui*lj)):
        a={}
        for ix,c in ((i,ai),(j,aj),(col,Q(az))):a[ix]=a.get(ix,Q(0))+c
        rows.append((a,bb))
    boxes += [boxes[i]*boxes[j] for i,j in pairs]
    if profile in ('CYCLE','PIVOT_CYCLE'):append(cycle_rows(aux))
    return rows,boxes

def coefficients(rows,boxes,record):
    if not isinstance(record,dict) or set(record)!={'coordinate','direction','objective_weight','weights'}:
        raise ValueError('Bad bound schema')
    i=record['coordinate'];sgn=record['direction'];t=record['objective_weight']
    if type(i)is not int or not 0<=i<24:raise ValueError('Bound must target a real image coordinate')
    if type(sgn)is not int or sgn not in(-1,1):raise ValueError('Bad bound direction')
    if type(t)is not int or t<=0:raise ValueError('Positive integer target multiplier required')
    weights=record['weights']
    if not isinstance(weights,list) or not weights:raise ValueError('Empty bound support')
    c=[Q(0)]*len(boxes);b=Q(0);seen=set()
    for pair in weights:
        if not isinstance(pair,list) or len(pair)!=2:raise ValueError('Bad support entry')
        j,w=pair
        if type(j)is not int or not 0<=j<len(rows) or j in seen:raise ValueError('Invalid/duplicate row')
        if type(w)is not int or w<=0:raise ValueError('Positive integer weights required')
        seen.add(j);a,bb=rows[j];b+=w*bb
        for h,v in a.items():c[h]+=w*v
    c[i]-=t*sgn
    return c,b,t

def bound_value(rows,boxes,record):
    c,b,t=coefficients(rows,boxes,record)
    return (b-sum(min(v*z.lo,v*z.hi) for v,z in zip(c,boxes)))/t

def dense_bound_value(rows,boxes,record):
    """Separate dense-dot-product evaluation, same frozen mathematical rows.
    This is an implementation cross-check, not a second independent B theorem.
    """
    coefficients(rows,boxes,record) # schema checks
    weights=dict(record['weights']);n=len(boxes)
    c=[sum(Q(weights[j])*rows[j][0].get(i,Q(0)) for j in weights) for i in range(n)]
    c[record['coordinate']]-=record['direction']*record['objective_weight']
    b=sum(Q(w)*rows[j][1] for j,w in weights.items())
    lower=sum(c[i]*(boxes[i].lo if c[i]>=0 else boxes[i].hi) for i in range(n))
    return (b-lower)/record['objective_weight']

def apply_wave(out,wave,label=None,profile='BASE',cross_check=False):
    if out['status']=='EMPTY':raise ValueError('Bounds after an empty enclosure')
    if not isinstance(wave,list) or not 1<=len(wave)<=48:raise ValueError('Bad bound wave')
    rows,boxes=rows_and_bounds(out['aux_image'],label,profile)
    values=[]
    for record in wave:
        value=bound_value(rows,boxes,record)
        if cross_check and value!=dense_bound_value(rows,boxes,record):raise AssertionError('Dual implementations differ')
        values.append(value)
    b=[I(*z) for z in out['aux_image']]
    try:
      for record,value in zip(wave,values):
        if record['direction']==1:fs.meet(b,record['coordinate'],hi=value)
        else:fs.meet(b,record['coordinate'],lo=-value)
    except fs.Empty as err:return {'status':'EMPTY','reason':'dual_intersection_'+str(err)}
    return common_contract({'status':'BOUNDED','aux_image':[z.data() for z in b]},label,profile)

def replay_trace(box,trace,label=None,cross_check=False,allow_open=False):
    if not isinstance(trace,dict) or set(trace)!={'profile','waves','terminal'}:raise ValueError('Bad trace schema')
    profile=trace['profile'];validate_profile(profile)
    waves=trace['waves']
    if not isinstance(waves,list) or len(waves)>128:raise ValueError('Bad wave list')
    out=common_contract(fs.parent_enclosure(box),label,profile)
    for wave in waves:out=apply_wave(out,wave,label,profile,cross_check)
    terminal=trace['terminal']
    if not isinstance(terminal,dict):raise ValueError('Missing terminal')
    kind=terminal.get('kind')
    if kind=='O':
      if terminal!={'kind':'O'} or not allow_open:raise ValueError('Unpaid trace')
      return {'status':'OPEN','waves':len(waves),'bounds':sum(map(len,waves)),'aux_image':out.get('aux_image')}
    if kind=='I':
      if terminal!={'kind':'I'} or out['status']!='EMPTY':raise ValueError('False interval contradiction')
      return {'status':'EMPTY','waves':len(waves),'bounds':sum(map(len,waves))}
    if out['status']=='EMPTY':raise ValueError('Use I for an already empty enclosure')
    if kind=='A':
      if terminal!={'kind':'A'} or fs.safe_port(out['aux_image'])is None:raise ValueError('False alpha port')
      return {'status':'SAFE','waves':len(waves),'bounds':sum(map(len,waves))}
    if kind not in ('C','H'):raise ValueError('Unknown terminal')
    rows,boxes=rows_and_bounds(out['aux_image'],label,profile)
    margin=inherited.dual_margin(rows,boxes,terminal)
    if kind=='C' and margin>=0 or kind=='H' and margin>0:raise ValueError('Unproved terminal')
    return {'status':'EMPTY'if kind=='C'else'SAFE','waves':len(waves),'bounds':sum(map(len,waves)),'margin':str(margin)}
