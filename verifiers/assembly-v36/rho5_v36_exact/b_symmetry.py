"""Actual J0 M^T J0 and sign normalization for the negative-D B model.
The tail physical D/S/O entries are transposed and otherwise unchanged.
"""
from fractions import Fraction as Q
from gap_model import check_actual,physical_matrix,height

def normalized_transpose(z):
    z=list(map(Q,z));check_actual(z)
    assert z[2]==-z[1] and z[8]*z[9]>0
    p,k=z[7],z[0];out=z[:];out[8]=z[9];out[9]=z[8]
    for i in range(3):
        out[10+i]=z[16+i];out[16+i]=z[10+i]
        out[13+i]=-z[19+i]/p;out[19+i]=-p*z[13+i]
    out[3]=k*z[5];out[4]=k*z[6];out[5]=z[3]/k;out[6]=z[4]/k
    out[22],out[23]=z[23],z[22]
    # Actual diagonal sign congruences, never a change to a free packet.
    if out[8]<0:
        out[8]=-out[8];out[9]=-out[9]
        for j in list(range(13,16))+list(range(19,22)):out[j]=-out[j]
    if out[13]<0:
        for j in range(10,22):out[j]=-out[j]
    if out[3]>0:
        for j in (3,4,5,6,11,12,14,15,17,18,20,21):out[j]=-out[j]
    check_actual(out);assert out[8]>0 and out[9]>0 and out[13]>=0 and out[3]<=0
    assert height(out)==height(z) and out[22]+out[23]==z[22]+z[23]
    mats0=physical_matrix(z);mats1=physical_matrix(out)
    for a,b in zip(mats0[1:],mats1[1:]):
        for i in (1,2):
            for j in (1,2):assert b[i][j]==a[j][i]
    return out
