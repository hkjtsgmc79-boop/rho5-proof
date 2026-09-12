#!/usr/bin/env python3
"""Independent exact acceptance. Does NOT import any optimizer/discovery module.
Checks inherited root partition, then verifies every graft as an exact
implication tree (binary cuts, Farkas contractions, contradictions, or Q).
"""
import ctypes,json,gzip,subprocess,time,argparse,sys
from pathlib import Path
from fractions import Fraction as Q
import array, os
BASE=Path(__file__).resolve().parent;S=1<<40
ROOTLO=list(map(Q,['1/4','1/16','1/16','0','1/2','0']))
ROOTHI=list(map(Q,['7/8','1','7/8','1','1','7/8']))
QLO=list(map(Q,['617/1000','1947/2500','181/400','12169/12500','49999/50000','243/1250']))
QHI=list(map(Q,['6181/10000','1559/2000','227/500','97361/100000','1','39/200']))
F=Q(4132517,1000000)
C=ctypes

def require(test,message):
    if not test:raise ValueError(message)

def build():
    so=BASE/'libeval_verify.so'
    subprocess.run([os.environ.get('CXX','g++'),'-O2','-std=c++17','-fPIC',('-dynamiclib' if sys.platform=='darwin' else '-shared'),str(BASE/'eval.cpp'),str(BASE/'eval_taylor.cpp'),'-o',str(so)],check=True)
    lib=C.CDLL(str(so));ptr=C.POINTER(C.c_int64)
    lib.eval.argtypes=[ptr,ptr,C.c_int64,C.c_int64,ptr,ptr]
    lib.eval_taylor.argtypes=lib.eval.argtypes
    return lib
LIB=None

def evaluate(lo,hi,mode='M'):
    LA=(C.c_int64*6)(*lo); HA=(C.c_int64*6)(*hi);b=(C.c_int64*74)();r=(C.c_int64*(37*7))()
    require(LIB.eval(LA,HA,F.numerator,F.denominator,b,r)==0,'interval overflow/evaluation failure')
    m=36 if b[72]>=0 else 35
    base=[list(r[7*j:7*j+7]) for j in range(m)]
    if mode=='M':return list(b),base
    require(mode=='MT','unsupported arithmetic mode')
    bt=(C.c_int64*74)();rt=(C.c_int64*(37*7))()
    require(LIB.eval_taylor(LA,HA,F.numerator,F.denominator,bt,rt)==0,'Taylor overflow/evaluation failure')
    require(list(b)==list(bt),'natural interval mismatch')
    tr=[list(rt[7*j:7*j+7]) for j in range(m)]
    rows=base[:35]+tr[:35]+([base[35],tr[35]] if m==36 else [])
    return list(b),rows

def weighted(rows,w):
    require(isinstance(w,list) and len(w)>0,'empty weights')
    seen=set();z=[0]*7
    for item in w:
        require(isinstance(item,list) and len(item)==2,'weight record')
        j,ww=item
        require(type(j) is int and 0<=j<len(rows) and j not in seen,'invalid/duplicate guard')
        require(type(ww) is int and ww>0,'nonpositive/noninteger weight')
        seen.add(j)
        for i in range(7):z[i]+=rows[j][i]*ww
    return z

def prefix(cp):
    require(Q(cp['f'])==F,'wrong f')
    require(list(map(Q,cp['root_lo']))==ROOTLO and list(map(Q,cp['root_hi']))==ROOTHI,'wrong root')
    require(list(map(Q,cp['target_lo']))==QLO and list(map(Q,cp['target_hi']))==QHI,'wrong target')
    allterms=cp['closed_leaves']+cp['inside_target_leaves']+[dict(l,kind='open') for l in cp['open_frontier']];terms={int(l['node']):l for l in allterms}
    require(len(terms)==len(allterms),'duplicate inherited terminal')
    widths=[b-a for a,b in zip(ROOTLO,ROOTHI)]; stack=[(ROOTLO,ROOTHI,0,1)];visited=set();counts={'nodes':0,'combo':0,'interval':0,'inside':0,'open':0}
    while stack:
        lo,hi,depth,nid=stack.pop();counts['nodes']+=1
        require(counts['nodes']<=2*len(allterms)+1,'malformed inherited partition')
        if nid not in terms:
            scores=[(lo[i]<QLO[i] or hi[i]>QHI[i],(hi[i]-lo[i])/widths[i]) for i in range(6)]
            d=max(range(6),key=lambda i:scores[i]);mid=(lo[d]+hi[d])/2
            lhi=list(hi);lhi[d]=mid;rlo=list(lo);rlo[d]=mid
            stack.extend([(rlo,hi,depth+1,2*nid+1),(lo,lhi,depth+1,2*nid)])
            continue
        rec=terms[nid];visited.add(nid)
        require(rec['depth']==depth and list(map(Q,rec['lo']))==lo and list(map(Q,rec['hi']))==hi,'inherited box mismatch')
        kind=rec['kind'];counts[kind]+=1
        if kind=='open':continue
        if kind=='inside':
            require(all(lo[i]>=QLO[i] and hi[i]<=QHI[i] for i in range(6)),'inherited Q miss');continue
        require(all((x*S).denominator==1 for x in lo+hi),'non-grid inherited box')
        bd,rows=evaluate([int(a*S) for a in lo],[int(a*S) for a in hi])
        if kind=='interval':
            j=rec['guard'];require(type(j) is int and 0<=j<len(rows) and bd[2*j+1]<0,'inherited direct failure')
        elif kind=='combo':
            z=weighted(rows,rec['weights']);require(z[0]+sum(abs(a) for a in z[1:])<0,'inherited Farkas failure')
        else:raise ValueError('inherited unexpected kind')
    require(visited==set(terms),'unvisited inherited terminal')
    return counts

def graft(front,folder):
    nid0=int(front['node']); path=folder/f'front_{nid0}.jsonl.gz'
    counts={k:0 for k in ('I','F','C','B','Q','E')}; counts['cut_certificates']=0
    lo=[int(Q(x)*S) for x in front['lo']];hi=[int(Q(x)*S) for x in front['hi']]
    started=time.time();n=0
    with gzip.open(path,'rt',encoding='utf-8') as fp:
        header=json.loads(next(fp))
        require(header['format']=='V28_EXACT_GRID_TREE_V1' and header['grid_bits']==40,'graft format')
        require(header['front']==nid0 and Q(header['f'])==F and header['root_lo']==lo and header['root_hi']==hi,'graft root mismatch')
        stack=[(lo,hi,1)]
        for line in fp:
            require(len(stack)>0,'extra record');lo,hi,nid=stack.pop();r=json.loads(line);n+=1
            require(r['node']==nid,'graft traversal mismatch')
            k=r['kind'];require(k in counts,'OPEN or unknown proof kind');counts[k]+=1
            if k=='E':require(any(lo[i]>hi[i] for i in range(6)),'nonempty E');continue
            require(all(lo[i]<=hi[i] for i in range(6)),'invalid box')
            if k=='Q':
                require(all(Q(lo[i],S)>=QLO[i] and Q(hi[i],S)<=QHI[i] for i in range(6)),'Q containment');continue
            if k=='B':
                d=r['axis'];c=r['cut'];require(type(d) is int and 0<=d<6 and type(c) is int and lo[d]<c<hi[d],'invalid split')
                lhi=list(hi);lhi[d]=c;rlo=list(lo);rlo[d]=c
                stack.extend([(rlo,hi,2*nid+1),(lo,lhi,2*nid)]);continue
            bd,rows=evaluate(lo,hi,r.get('mode','M'))
            if k=='I':
                j=r['guard'];require(type(j) is int and 0<=j<(36 if bd[72]>=0 else 35) and bd[2*j+1]<0,'invalid direct leaf');continue
            if k=='F':
                z=weighted(rows,r['weights']);require(z[0]+sum(abs(a) for a in z[1:])<0,'invalid Farkas leaf');continue
            require(k=='C' and len(r['cuts'])>0,'invalid contraction')
            cen=[(l+h)//2 for l,h in zip(lo,hi)];rad=[max(h-c,c-l) for l,h,c in zip(lo,hi,cen)];nlo=list(lo);nhi=list(hi)
            for d,side,c,w in r['cuts']:
                require(type(d) is int and 0<=d<6 and side in ('lo','hi') and type(c) is int and lo[d]<c<hi[d],'invalid cut')
                z=weighted(rows,w);A=z[d+1]
                require(A>0 if side=='lo' else A<0,'cut direction')
                B=z[0]+sum(abs(z[i+1]) for i in range(6) if i!=d)
                require(B*rad[d]+A*(c-cen[d])<0,'uncertified removed slab')
                if side=='lo':nlo[d]=max(nlo[d],c)
                else:nhi[d]=min(nhi[d],c)
                counts['cut_certificates']+=1
            stack.append((nlo,nhi,2*nid))
        require(len(stack)==0,'unfinished graft')
    print('GRAFT_EXACT_PASS',nid0,n,counts,round(time.time()-started,3),flush=True)
    return {'front':nid0,'nodes':n,'counts':counts,'seconds':time.time()-started}

def main():
    global LIB
    ap=argparse.ArgumentParser();ap.add_argument('--front',type=int);ap.add_argument('--cert-dir',default='certs');args=ap.parse_args()
    LIB=build();cp=json.loads((BASE/'RHO5_V26_REBUILT/global_localization_partial_checkpoint.json').read_text())
    started=time.time();pre=prefix(cp);print('PREFIX_EXACT_PASS',pre,flush=True)
    fs=[x for x in cp['open_frontier'] if args.front is None or int(x['node'])==args.front]
    require(len(fs)>0,'no requested graft');records=[graft(f,BASE/args.cert_dir) for f in fs]
    status='V28_FULL_GLOBAL_LOCALIZATION_EXACT_PASS' if args.front is None else 'V28_SELECTED_GRAFT_EXACT_PASS'
    out={'status':status,'f':str(F),'prefix':pre,'grafts':records,'seconds':time.time()-started,'global_coverage':args.front is None,'open_grafts':0 if args.front is None else 13-len(fs)}
    (BASE/('coverage_verification.json' if args.front is None else f'graft_{args.front}_verification.json')).write_text(json.dumps(out,indent=2))
    print(status,flush=True)
if __name__=='__main__':main()
