from fractions import Fraction as Fr
import math
lam=Fr(37,40); al=Fr(3,40); H=lam+3*al
def fl(x): return math.floor(x)
def ell(x,z): return fl(x-z)+fl(x+z)+1
def psi(u):
    if u<=0: return Fr(0)
    c=math.ceil(u); return c*u - Fr(c*(c-1),2)
def zbreaks(x):
    # breakpoints of ell(x,z), ell(al x,z) for z in (0,1/2)
    bs={Fr(0),Fr(1,2)}
    for y in (x, al*x):
        f=y-fl(y)
        for b in (f,1-f):
            if 0<b<Fr(1,2): bs.add(b)
    return sorted(bs)
def phi(x,k):
    bs=zbreaks(x); s=Fr(0)
    for a,b in zip(bs,bs[1:]):
        z=(a+b)/2
        c=3*ell(al*x,z)-Fr(ell(x,z)+4,2)
        s+=(b-a)*psi(k-c)
    return lam*x*k - s
def J(u):
    m=fl(2*u); return m*u-Fr(m*(m+1),4)
def Nf(x): return 2*lam*x*fl(x)-12*lam*x*fl(al*x)-2*J(lam*x)
def Rin(x):
    best=None
    k0=math.floor(2*(2*H*x))  # rough
    for kk in range(-40, 4*int(x)+40):
        k=Fr(kk,2); v=phi(x,k)
        if best is None or v>best[0]: best=(v,k)
    return -2*best[0]-Nf(x), best[1]
def Gam(x):
    T=fl(2*H*x); s=H*x-Fr(T,2); q=fl(2*x); npl=(2*x-q)/2
    bs=zbreaks(x); I=Fr(0)
    for a,b in zip(bs,bs[1:]):
        z=(a+b)/2; l=ell(x,z); bb=3*ell(al*x,z)
        I+=(b-a)*(T-bb)*(T+bb-l-5)
    return I + s*(2*T-q-5) + max(Fr(0),s-npl)
def Rpap(x): return -Gam(x)-Nf(x)
import random
for x in [Fr(3),Fr(7,2)+Fr(1,1000),Fr(5)+Fr(1,3),Fr(11)+Fr(7,10),Fr(19)+Fr(1,7), Fr(40)+Fr(2,9)]:
    r,k=Rin(x); print(float(x), float(r), float(Rpap(x)), float(k), float(2*H*x))
