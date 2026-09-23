import sys, time, math
from flint import fmpq, fmpz, fmpq_poly, fmpz_poly, fmpq_mat, arb, arb_poly, ctx

def Dpoly(m):
    p = fmpz_poly([1])
    for j in range(1, m+1):
        p *= fmpz_poly([j*j, 1])
    return p

def entries(n):
    K, N, h = 40*n, 3*n, 37*n
    DN, DK = Dpoly(N), Dpoly(K)
    W = DN**6
    E = 2*h - 1
    maxk = max(0, 6*N + E - 1 - K)
    mus = [fmpq(-1)**k * fmpq.bernoulli(2*k+2) * ((2*k+3)*(2*k+4)*(2*k+5)) / 24 for k in range(maxk+1)]
    H5 = [fmpq(0)]
    for j in range(1, K+1): H5.append(H5[-1] + fmpq(1, j**5))
    base = {}
    for j in range(N+1, K+1):
        num = fmpq(DN(fmpz(-j*j)))**6
        den = fmpq(1)
        for k in range(1, K+1):
            if k != j: den *= (k*k - j*j)
        base[j] = num/den
    Wq, DKq = fmpq_poly(W), fmpq_poly(DK)
    a, b = [], []
    for e in range(E):
        Pe = (Wq * fmpq_poly([0]*e+[1])) // DKq
        ae = fmpq(0)
        for k in range(Pe.degree()+1):
            ae += Pe[k]*mus[k]
        be = fmpq(0)
        for j in range(N+1, K+1):
            c = base[j] * fmpq(-j*j)**e
            be += c * (j**4)
            ae += c * (-fmpq(j**4)*H5[j] - fmpq(1,4) + fmpq(1, 2*j))
        a.append(ae); b.append(be)
    return K, N, h, a, b

def det_poly(h, a, b):
    A = fmpq_mat(h, h, [a[i+j] for i in range(h) for j in range(h)])
    B = fmpq_mat(h, h, [b[i+j] for i in range(h) for j in range(h)])
    detB = B.det()
    C = -(B.inv() * A)
    return C.charpoly() * detB

def logfact(m): return math.lgamma(m+1)

def run(n):
    t0 = time.time()
    K, N, h, a, b = entries(n)
    t1 = time.time()
    Delta = det_poly(h, a, b)
    t2 = time.time()
    assert Delta.degree() == h, Delta.degree()
    # check (2.9): leading coefficient
    DN = Dpoly(N); lead = fmpq((-1)**((h*(h-1))//2))
    for j in range(N+1, K+1): lead *= fmpq(j**4) * fmpq(DN(fmpz(-j*j)))**5
    print(f"  (2.9) leading coeff check: {Delta[h] == lead}")
    # S_K
    logS = 2*h*logfact(K) + (h-1)*math.log(4) - 12*h*logfact(N) - 2*sum(logfact(2*i) for i in range(1, h))
    # content of Delta: gcd(numerators)/lcm(denominators)
    coeffs = [Delta[i] for i in range(h+1)]
    from math import gcd, lcm
    g = 0; l = 1
    for c in coeffs:
        g = gcd(g, int(c.p)); l = lcm(l, int(c.q))
    # primitive P = Delta * l / g  (integer coefficients, gcd 1)
    P = fmpz_poly([int(c.p) * (l // int(c.q)) // g for c in coeffs])
    maxbits = max(abs(int(P[i])).bit_length() for i in range(h+1))
    ctx.prec = maxbits + K*K + 4000
    z5 = arb(5).zeta()
    Pz = arb_poly([int(P[i]) for i in range(h+1)])(z5)
    Dz = fmpq_poly_eval_arb(Delta, z5, h)
    logcont = math.log(g) - math.log(l)          # log content(Delta)
    logP = float(Pz.log())
    logD = float(Dz.log())
    logF = logD + logS
    logcontF = logcont + logS                     # log content(F_K) = log(1/m_min)
    print(f"n={n} K={K} h={h}  times: entries {t1-t0:.1f}s det {t2-t1:.1f}s")
    print(f"  Delta_K(z5)          = {Dz.str(10)}   log = {logD:.3f}")
    print(f"  log S_K              = {logS:.3f}")
    print(f"  log F_K(z5)          = {logF:.3f}    /K^2 = {logF/K**2:.5f}   (paper claims <= U = -1.36700 eventually)")
    print(f"  log content(F_K)     = {logcontF:.3f}    -log content /K^2 = {-logcontF/K**2:.5f}   (paper: log m_K,M /K^2 <= A_200 = 1.34960 eventually)")
    print(f"  P_K(z5) primitive    = {Pz.str(10)}   log = {logP:.3f}   /K^2 = {logP/K**2:.5f}   /n^2 = {logP/n**2:.3f}   (paper: <= -27.8 n^2 eventually)")
    print(f"  max |coeff P_K| bits = {maxbits}, log H(P_K)/K^2 = {maxbits*math.log(2)/K**2:.4f}")
    sys.stdout.flush()

def fmpq_poly_eval_arb(poly, z, h):
    num = arb_poly([int(poly[i].p) for i in range(h+1)])  # careful: different denominators
    # evaluate exactly: sum coeff * z^i with arb rationals
    s = arb(0); zp = arb(1)
    for i in range(h+1):
        c = poly[i]
        s += arb(int(c.p)) / arb(int(c.q)) * zp
        zp *= z
    return s

if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        run(n)
