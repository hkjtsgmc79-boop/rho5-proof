#!/usr/bin/env python3
"""Independent symbolic Schur reconstruction from the actual 5x5 matrix."""
from pathlib import Path
import json,sympy as s
ROOT=Path(__file__).resolve().parent

def main():
 k,r,w,A,B,c,d,p,e,be=s.symbols('k r w A B c d p e be',nonzero=True)
 u=s.Matrix(s.symbols('u0:3'));x=s.Matrix(s.symbols('x0:3'));v=s.Matrix(s.symbols('v0:3'));q=s.Matrix(s.symbols('q0:3'))
 D=s.Matrix([[k,A,B],[c*k,r+c*A,r+c*B],[d*k,r+d*A,w+d*B]])
 S=D+x*q.T;O=S+u*v.T
 M=s.zeros(5);M[0,0]=1;M[0,1]=-e;M[0,2:5]=v.T;M[1,0]=be;M[1,1]=p-e*be;M[1,2:5]=(q+be*v).T
 M[2:5,0]=u;M[2:5,1]=p*x-e*u;M[2:5,2:5]=O
 def schur(T):return (T[1:,1:]-T[1:,0]*T[0,1:]/T[0,0]).applyfunc(s.cancel)
 first=schur(M);expected=s.zeros(4);expected[0,0]=p;expected[0,1:]=q.T;expected[1:,0]=p*x;expected[1:,1:]=S
 checks=0
 for a,b in zip(first,expected):assert s.cancel(a-b)==0;checks+=1
 second=schur(first)
 for a,b in zip(second,D):assert s.cancel(a-b)==0;checks+=1
 third=schur(second)
 for a,b in zip(third,s.Matrix([[r,r],[r,w]])):assert s.cancel(a-b)==0;checks+=1
 fourth=schur(third);assert s.cancel(fourth[0]-(w-r))==0;checks+=1
 assert s.cancel(M[:3,:3].det()-p*k)==0;checks+=1
 # Physical labels reconstructed independently from matrix entries/stages.
 vals={'e':e,'beta':be,'head':p-e*be};bounds={key:s.S(1)for key in vals}
 for i in range(3):
  for key,val,bd in [(f'u{i}',u[i],1),(f'x{i}',x[i],1),(f'v{i}',v[i],1),(f'q{i}',q[i],p),(f'L{i}',M[i+2,1],1),(f'P{i}',M[1,i+2],1)]:vals[key]=val;bounds[key]=s.S(bd)
  for j in range(3):
   for key,val,bd in [(f'D{i}{j}',second[i,j],k),(f'S{i}{j}',first[i+1,j+1],p),(f'O{i}{j}',M[i+2,j+2],1)]:vals[key]=val;bounds[key]=s.S(bd)
 # Symbols must use the same plain identifiers, with assumptions removed.
 subs={z:s.Symbol(str(z))for z in M.free_symbols|{k,r,w,A,B,c,d,p,e,be}}
 phys={key+sign:s.expand((bd-val if sign=='+' else bd+val).xreplace(subs))for key,val in vals.items()for bd in [bounds[key]]for sign in ['+','-']}
 phys={name:expr for name,expr in phys.items()if expr!=0};assert len(phys)==95
 for typ in ('I','II'):
  data=json.loads((ROOT/'models'/f'{typ}214'/'model.json').read_text());rows=data['rows'][:95]
  assert {r['name']for r in rows}==set(phys)
  loc={name:s.Symbol(name)for name in data['variables']}
  for row in rows:assert s.expand(s.sympify(row['polynomial'],locals=loc)-phys[row['name']])==0;checks+=1
 out={'status':'ACTUAL_MATRIX_SCHUR_AND_PHYSICAL_ROW_DICTIONARY_PASS','symbolic_assertions':checks,'physical_rows_per_model':95}
 (ROOT/'logs/semantic_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
