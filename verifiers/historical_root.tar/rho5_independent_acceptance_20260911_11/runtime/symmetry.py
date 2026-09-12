"""Two actual negative-D tail symmetries; preserve CP and final height.
Q=diag(I3,J), J=[[0,-1],[1,0]]. Diagonal switch is M -> Q M Q,
NOT Q M Q^T. Afterward only legal diagonal sign congruences normalize.
"""
from fractions import Fraction as Q
from itertools import product
from capacity import rational,check_complete,matrices

def normalize(z):
    z=list(map(rational,z))
    if z[8]<0:
        z[8]=-z[8];z[9]=-z[9]
        for j in list(range(13,16))+list(range(19,22)):z[j]=-z[j]
    if z[13]<0:
        for j in range(10,22):z[j]=-z[j]
    if z[3]>0:
        for j in (3,4,5,6,11,12,14,15,17,18,20,21):z[j]=-z[j]
    return z

def diagonal_switch(z,normalized=True):
    z=list(map(rational,z));check_complete(z)
    if z[2]!=-z[1]:raise ValueError('negative D required')
    y=z[:];y[3]=z[4];y[4]=-z[3];y[5]=-z[6];y[6]=z[5]
    for off in (10,13):y[off+1]=-z[off+2];y[off+2]=z[off+1]
    for off in (16,19):y[off+1]=z[off+2];y[off+2]=-z[off+1]
    y[22],y[23]=z[23],z[22]
    if normalized:y=normalize(y)
    assert check_complete(y)['F']==check_complete(z)['F']
    return y

def transpose(z,normalized=True):
    z=list(map(rational,z));check_complete(z)
    if z[2]!=-z[1]:raise ValueError('negative D required')
    y=z[:];p=z[7];k=z[0];y[8],y[9]=z[9],z[8]
    y[3]=k*z[5];y[4]=k*z[6];y[5]=z[3]/k;y[6]=z[4]/k
    y[10:13]=z[16:19];y[16:19]=z[10:13]
    y[13:16]=[-v/p for v in z[19:22]];y[19:22]=[-p*v for v in z[13:16]]
    y[22],y[23]=z[23],z[22]
    if normalized:y=normalize(y)
    assert check_complete(y)['F']==check_complete(z)['F']
    return y

def switch_labels(labels):
    r,s,t=labels
    assert r[1:]in('11+','22-')
    return (r[0]+('22-'if r[1:]=='11+'else'11+'),t[0]+'12+',s[0]+'21+')

def transpose_labels(labels):
    r,s,t=labels;return(r,t[0]+'12+',s[0]+'21+')

def canonical_labels(labels):
    labels=tuple(labels);steps=[]
    if labels[0][1:]=='22-':labels=switch_labels(labels);steps.append('K')
    if 'DSO'.index(labels[1][0])>'DSO'.index(labels[2][0]):labels=transpose_labels(labels);steps.append('T')
    assert labels[0][1:]=='11+'
    return labels,steps

def actual_slacks(z):
    k,p=Q(z[0]),Q(z[7]);_,D,S,O=matrices(z)
    out={}
    for name,T,h in (('D',D,k),('S',S,p),('O',O,Q(1))):
        for i in (1,2):
            for j in (1,2):
                out[f'{name}{i}{j}+']=h-T[i][j];out[f'{name}{i}{j}-']=h+T[i][j]
    return out

def contact_orbits():
    labels=list(product([l+ij for ij in('11+','22-')for l in'DSO'],[l+'12+'for l in'DSO'],[l+'21+'for l in'DSO']))
    orbits={}
    for x in labels:
        y,steps=canonical_labels(x);orbits.setdefault(y,[]).append({'from':x,'operations':steps})
    assert len(labels)==54 and len(orbits)==18 and sum(map(len,orbits.values()))==54
    return orbits
