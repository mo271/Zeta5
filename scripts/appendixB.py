from fractions import Fraction as Fr
from math import floor
import random
random.seed(7)
lam = Fr(37,40); al = Fr(3,40); H = 1 + 2*al
def fl(x): return Fr(floor(x))
def ell(x, z): return fl(x - z) + fl(x + z) + 1
def frac(x): return x - fl(x)
def d0(u): return min(u, 1-u)
def Gamma(x):
    T = fl(2*H*x); s = H*x - T/2; q = fl(2*x); nplus = (2*x - q)/2
    # integrate (T - b)(T + b - l - 5) over z in (0,1/2): step functions with breakpoints d0({x}), d0({alpha x})
    bps = sorted(set([Fr(0), Fr(1,2), d0(frac(x)), d0(frac(al*x))]))
    I = Fr(0)
    for a, b in zip(bps, bps[1:]):
        if b <= a: continue
        z = (a + b)/2
        l = ell(x, z); bb = 3*ell(al*x, z)
        I += (T - bb)*(T + bb - l - 5)*(b - a)
    return I + s*(2*T - q - 5) + max(s - nplus, 0)
def J(u):
    m = fl(2*u); return m*u - m*(m+1)/4
def Nf(x): return 2*lam*x*fl(x) - 12*lam*x*fl(al*x) - 2*J(lam*x)
def R(x): return -Gamma(x) - Nf(x)
# breakpoints (B.2) in (3,20)
cs = [Fr(2), 2*al, 2*lam, 2*H, 4*al, 2*(1-al), 2*(1+al)]
pts = set([Fr(3), Fr(20)])
for c in cs:
    k = floor(3*c)
    while Fr(k)/c <= 20:
        x = Fr(k)/c
        if 3 < x < 20: pts.add(x)
        k += 1
pts = sorted(pts)
print("number of intervals:", len(pts)-1)
total = Fr(0); nonaffine = 0
for l, r in zip(pts, pts[1:]):
    x1, x2, x3 = (2*l+r)/3, (l+2*r)/3, (l+r)/2
    a = (R(x2) - R(x1))/(x2 - x1); b = R(x1) - a*x1
    if R(x3) != a*x3 + b: nonaffine += 1
    # also check at random rationals
    for t in [Fr(random.randint(1, 999), 1000) for _ in range(12)]:
        xt = l + t*(r-l)
        if R(xt) != a*xt + b: nonaffine += 1
    total += a*(1/l - 1/r) + b/2*(1/l**2 - 1/r**2)
print("non-affine pieces detected:", nonaffine)
paper518 = Fr(322437603634266857629, 7535670527041937280000)
print("int_3^20 R/x^3 =", total, "== (5.18):", total == paper518, float(total), float(paper518))
# Table 3 unit intervals
for j in range(3, 20):
    sub = Fr(0)
    for l, r in zip(pts, pts[1:]):
        if l >= j and r <= j+1:
            x1, x2 = (2*l+r)/3, (l+2*r)/3
            a = (R(x2) - R(x1))/(x2 - x1); b = R(x1) - a*x1
            sub += a*(1/l - 1/r) + b/2*(1/l**2 - 1/r**2)
    print(f"  [{j},{j+1}]: {sub}")
# Outer integral (5.10)
def R0(y):
    if Fr(1,3) < y < Fr(1,2): return 8 - 9*y - 8*al - 5*min(al, 1-2*y) - 5*max(1+al-3*y, 0)
    if Fr(1,2) < y < 1: return 7*(1-y) - 6*min(al, 1-y) - 6*max(1+al-2*y, 0) + max(1+4*al-2*y, 0)
    return Fr(0)
def dfun(y):
    if Fr(1,3) < y < Fr(1,2): return max(1 + 4*al - 3*y - max(1+al-3*y, 0), 0)
    return Fr(0)
def Tout(y): return R0(y) - dfun(y) - 2*lam*fl(1/y) + sum(max(2*lam - j*y, 0) for j in range(1,6))
# breakpoints of Tout on (1/3, 2*lam)
bp = set([Fr(1,3), 2*lam, Fr(1,2), Fr(1)])
bp |= {Fr(1,k) for k in range(1, 4)}
bp |= {(1-al)/2, (1+al)/3, (1+4*al)/3, (1+al)/2, (1+4*al)/2, 1 - al}
bp |= {2*lam/j for j in range(1,6)}
bp = sorted(b for b in bp if Fr(1,3) <= b <= 2*lam)
Iout = Fr(0); bad = 0
for l, r in zip(bp, bp[1:]):
    y1, y2, y3 = (2*l+r)/3, (l+2*r)/3, (l+r)/2
    c = (Tout(y2)-Tout(y1))/(y2-y1); b = Tout(y1) - c*y1
    for _ in range(12):
        t = Fr(random.randint(1, 999), 1000); yt = l + t*(r-l)
        if Tout(yt) != b + c*yt: bad += 1
    Iout += b*(r-l) + c*(r*r - l*l)/2
print("I_out =", Iout, "== 127751/96000:", Iout == Fr(127751,96000), " non-affine:", bad)
# A* consistency
Astar = paper518 + Fr(127751,96000) - Fr(2689,48000)
print("A* from (5.18)+(5.10)-(5.16):", Astar, "== paper (5.19):", Astar == Fr(9928298118277006344769, 7535670527041937280000))
# (5.14): bounds on Q(x) = R(x) - x F(x) sampled
def F(x): return 4*lam + 2*lam*frac(x) - 12*lam*frac(al*x)
mn, mx = Fr(10), Fr(-10)
import random
random.seed(1)
for _ in range(20000):
    x = Fr(random.randint(3000, 200000), 1000) + Fr(random.randint(0,999), 1000000)
    Q = R(x) - x*F(x); mn = min(mn, Q); mx = max(mx, Q)
print("sampled Q(x) range:", float(mn), float(mx), " paper: [-1/2, 13/8]")
