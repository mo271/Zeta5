from fractions import Fraction as Fr
import math
lam=Fr(37,40); al=Fr(3,40)
def fl(x): return math.floor(x)
def lrow(k,b):
    t=k-b+1
    return max(0, t//2)
def psiR(k,b):
    L=lrow(k,b); t=k-b
    return Fr(L*(t-L+1),2)
def bcoef(h): return [h(0), h(1)-h(0), h(2)-h(1)]
def cvLo(f): return [Fr(0),Fr(0),1-f]
def cvHi(f): return [Fr(1,2),f,Fr(1,2)]
def ccount(f,g,i,j):
    return max(Fr(0), min(min(cvHi(f)[i],cvHi(g)[j]),Fr(1,2)) - max(max(cvLo(f)[i],cvLo(g)[j]),Fr(0)))
def Jc(u):
    return sum(max(Fr(0),u-Fr(j,2)) for j in range(1,1001))
def Jc_fast(u):
    mu=fl(2*u); return mu*u-Fr(mu*(mu+1),4)
def Ein(x,k):
    q=fl(x); qq=fl(al*x); f=x-q; g=al*x-qq
    B=12*qq-2*q-4
    h=lambda a,b: psiR(k,B+6*b-a)
    # do properly
    s=Fr(0)
    for i in range(3):
        for j in range(3):
            c=bcoef(lambda a: bcoef(lambda b: h(a,b))[j])[i]
            s+=c*ccount(f,g,i,j)
    u=lam*x
    return -2*u*q+12*u*qq+2*Jc_fast(u)-u*k+2*s
# compare with paper R at test points
from growth import Rin
for x in [Fr(3),Fr(7,2)+Fr(1,1000),Fr(5)+Fr(1,3),Fr(11)+Fr(7,10),Fr(19)+Fr(1,7)]:
    r,kap=Rin(x)
    best=min(Ein(x,k) for k in range(-50,100))
    print(float(x), float(r), float(best))
