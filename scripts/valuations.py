import sys, math
from math import gcd, lcm
from flint import fmpq, fmpz
from hankel import entries, det_poly, Dpoly
from sympy import primerange

def vp(x, p):
    x = int(x); 
    if x == 0: return 10**9
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
def legendre(m, p):
    s = 0; q = p
    while q <= m: s += m // q; q *= p
    return s
def vS(K, N, h, p):
    return 2*h*legendre(K,p) - 12*h*legendre(N,p) - 2*sum(legendre(2*i,p) for i in range(1,h)) + (h-1)*(2 if p == 2 else 0)

def run(n):
    K, N, h, a, b = entries(n)
    Delta = det_poly(h, a, b)
    g = 0; l = 1
    for i in range(h+1):
        c = Delta[i]; g = gcd(g, int(c.p)); l = lcm(l, int(c.q))
    print(f"n={n} K={K} N={N} h={h}")
    bad = []
    rest_g, rest_l = g, l
    for p in primerange(2, 2*h+1):
        vg, vl = vp(g,p), vp(l,p); rest_g //= p**vg; rest_l //= p**vl
        vD = vg - vl                     # v_p of content(Delta_K)
        vF = vS(K,N,h,p) + vD           # v_p^G(F_K)
        b312 = -6*h*int(math.floor(math.log(5*K)/math.log(p)+1e-12)) - h*vp(24,p)
        ok312 = vF >= b312
        # Prop 4.3 outer range
        note = ""
        cond49 = p >= 7 and p <= K < 3*p and p*p > 2*K and 2*N < p and 5*N <= 2*p-2
        if cond49:
            v = K - p*(K//p); u = max(0, N+v-p+1); tp = min(N,v)+u; rp = max(0, K+4*N-2*p+2)
            if K < 2*p: gam = -7*(K-p) + 6*tp - 1 - min(rp, p-1-N+u)
            else:       gam = -7*(K-p) + 3 + 12*N + 5*tp - min(rp, p+u)
            ok43 = vD >= gam
            note = f" | Prop4.3: v_p(cont Delta)={vD} >= gamma_out={gam}: {ok43}"
            if not ok43: bad.append(('4.3', p, vD, gam))
        elif p > K:
            ok = vD >= 0; note = f" | p>K: v_p(cont Delta)={vD} >= 0: {ok}"
            if not ok: bad.append(('4.3b', p, vD, 0))
        if not ok312: bad.append(('3.12', p, vF, b312))
        if p > K//3 or p < 8:
            print(f"  p={p:4d}: v_p(cont Delta)={vD:5d}  v_p(S)={vS(K,N,h,p):6d}  v_p^G(F)={vF:6d} >= (3.12) bound {b312:6d}: {ok312}{note}")
    print(f"  leftover numerator gcd factor (primes > 2h): {rest_g}   leftover denominator factor: {rest_l}")
    print(f"  VIOLATIONS: {bad if bad else 'none'}")
    sys.stdout.flush()

for n in map(int, sys.argv[1:]): run(n)
