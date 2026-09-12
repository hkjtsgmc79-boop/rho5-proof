"""Closed rational intervals. No floating arithmetic enters a decision."""
from fractions import Fraction as Q

def rational(x):
    if isinstance(x,bool) or isinstance(x,float):
        raise TypeError('Use exact integers, rational strings, or Fraction; not bool/float')
    return Q(x)

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I) and b is None:
            self.lo,self.hi=a.lo,a.hi
        else:
            self.lo=rational(a); self.hi=rational(a if b is None else b)
        if self.lo>self.hi:raise ValueError('Reversed interval')
    def __add__(self,o):
        o=I(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o);v=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o)
        if o.lo<=0<=o.hi:raise ZeroDivisionError('No division through zero')
        return self*I(1/o.hi,1/o.lo)
    def __abs__(self):
        return I(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def data(self):return [str(self.lo),str(self.hi)]
    def is_zero(self):return self.lo==self.hi==0

def serial(x):
    if isinstance(x,I):return x.data()
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):serial(v)for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v)for v in x]
    return x
