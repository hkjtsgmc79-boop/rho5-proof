"""B17 native exact backend. Python preserves the reference input/ownership protocol."""
from pathlib import Path
from fractions import Fraction as Q
import ctypes, hashlib, json, os
from interval_capacity import I, ALPHA

ROOT=Path(__file__).resolve().parent
ENCLOSURE='high_value_v1'
_engine=None

class Engine:
    def __init__(self):
        self.library=ctypes.CDLL(os.environ.get('B17_NATIVE_LIB',str(ROOT/'libb17_native.so')))
        self.library.b17_create.argtypes=[];self.library.b17_create.restype=ctypes.c_void_p
        self.library.b17_request.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
        self.library.b17_request.restype=ctypes.c_char_p
        self.library.b17_destroy.argtypes=[ctypes.c_void_p];self.library.b17_destroy.restype=None
        self.library.b17_last_error.argtypes=[];self.library.b17_last_error.restype=ctypes.c_char_p
        self.handle=self.library.b17_create()
        if not self.handle:raise RuntimeError('Native frozen-data initialization failed: '+self.library.b17_last_error().decode())
        identities=self.request({'mode':'identity'})
        for name,digest in identities.items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('Native/source identity mismatch: '+name)
    def request(self,data):
        result=json.loads(self.library.b17_request(self.handle,json.dumps(data,separators=(',',':')).encode()))
        if 'error' in result:raise ValueError(result['error'])
        if 'complete_prefix_charts' in result:
            result['complete_prefix_charts']=result['complete_prefix_charts']=='true'
        if 'contraction_rounds' in result:result['contraction_rounds']=int(result['contraction_rounds'])
        return result

def engine():
    global _engine
    if _engine is None:_engine=Engine()
    return _engine

def box_data(box):
    return [(b if isinstance(b,I)else I(*b)).data() for b in box]

def oracle(box,*,local_ports=True,enclosure=None):
    request={'mode':'oracle','box':box_data(box),'local_ports':local_ports}
    if enclosure is not None:request['enclosure']=enclosure
    return engine().request(request)

def validate_record(record):
    if not isinstance(record,dict):raise ValueError('bad leaf')
    if 'enclosure' in record and record['enclosure']!=ENCLOSURE:raise ValueError('unknown enclosure version')
    kind=record.get('kind')
    if kind=='E':return
    if kind not in ('C','H'):raise ValueError('unknown certificate')
    weights=record.get('weights')
    if not isinstance(weights,list)or not weights:raise ValueError('empty weights')
    seen=set()
    for item in weights:
        if not isinstance(item,list)or len(item)!=2:raise ValueError('bad support pair')
        i,w=item
        if type(i)is not int or type(w)is not int or i<0 or i>=258 or w<=0 or i in seen:
            raise ValueError('bad row/weight')
        seen.add(i)
    if kind=='H'and(type(record.get('objective_weight'))is not int or record['objective_weight']<=0):
        raise ValueError('bad objective weight')

def verify_leaf(box,record):
    validate_record(record)
    result=engine().request({'mode':'leaf','box':box_data(box),'record':record})
    return result['leaf_status']

def margin(aux,record):
    validate_record(record)
    return Q(engine().request({'mode':'margin_aux','aux':box_data(aux),'record':record})['margin'])

def rows_and_bounds(aux):
    result=engine().request({'mode':'rows_aux','aux':box_data(aux)})
    rows=[({int(i):Q(c)for i,c in row},Q(rhs))for row,rhs in zip(result['rows_exact'],result['rhs_exact'])]
    return rows,[I(*x)for x in result['product_bounds']]

def propose(box,*,height=True):
    import numpy as np
    from scipy.optimize import linprog
    from relaxation import N,FI
    encoded=box_data(box)
    result=engine().request({'mode':'prepare','box':encoded,'enclosure':ENCLOSURE})
    if result['status']in('EMPTY','SAFE'):return {'kind':'E','enclosure':ENCLOSURE}
    center=np.asarray(result['center'],dtype=float);half=np.asarray(result['half'],dtype=float)
    mat=np.zeros((len(result['rows_float']),N));rhs=np.asarray(result['rhs_float'],dtype=float)
    for i,row in enumerate(result['rows_float']):
        for j,c in row:mat[i,int(j)]=float(c)
    bb=rhs-mat@center;aa=mat*half
    normal=np.maximum(1e-9,np.maximum(np.abs(bb),np.max(np.abs(aa),axis=1)))
    aa/=normal[:,None];bb/=normal
    phase=np.column_stack([aa,-np.ones(len(rhs))]);obj=np.zeros(N+1);obj[-1]=1
    res=linprog(obj,A_ub=phase,b_ub=bb,bounds=[(-1,1)]*N+[(0,None)],method='highs',options={'time_limit':10})
    def rationalize(lambdas,kind):
        if not np.all(np.isfinite(lambdas)):return None
        for scale in (10**6,10**9,10**12):
            weights=[max(0,int(round(float(v)*scale)))for v in lambdas]
            record={'kind':kind,'weights':[[i,w]for i,w in enumerate(weights)if w],'enclosure':ENCLOSURE}
            if kind=='H':record['objective_weight']=scale
            if not record['weights']:continue
            try:verify_leaf(box,record);return record
            except ValueError:pass
        return None
    if res.success and res.fun>1e-10:
        cert=rationalize(-res.ineqlin.marginals/normal,'C')
        if cert:return cert
    if height:
        obj=np.zeros(N);obj[FI]=-half[FI]
        result_lp=linprog(obj,A_ub=aa,b_ub=bb,bounds=[(-1,1)]*N,method='highs',options={'time_limit':10})
        if result_lp.success:
            cert=rationalize(-result_lp.ineqlin.marginals/normal,'H')
            if cert:return cert
    return None

def install():
    """Select this separately versioned backend; source reference files stay unchanged."""
    import tree_protocol,probe
    tree_protocol.verify_leaf=verify_leaf
    probe.propose=propose
