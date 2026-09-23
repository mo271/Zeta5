from mpmath import mp, mpf, log, sqrt, atan, pi
mp.dps = 30
T = [(3906748086,8992695531,10515596180),(2312248264,15340997855,29471737793),(1402286665,25730180724,42934365099),(881725356,41909578246,58204231966),(578197906,65851089563,69037621310),(396324613,99481037884,78873099189),(283911191,144325727458,84856120711),(212206188,201105762729,88396082127),(165097686,269345996903,88303382125),(133347132,347089554156,85472321255),(111522114,430806704415,78899184238),(96349355,515561896511,70353471918),(85815639,595448778546,58838976615),(78667711,664241383483,44421321106),(74129565,716160577112,30462865791),(71741310,746637295669,5959622577)]
D = mpf(10)**12
a = [mpf(x[0])/D for x in T]; b = [mpf(x[1])/D for x in T]; c = [mpf(x[2])/D for x in T]
al = mpf(3)/40; lam = mpf(37)/40; M0 = mpf(-1329)/200
def Uw(aa, bb, t):
    if aa <= t <= bb: return log((bb-aa)/4)
    m = (aa+bb)/2
    return log((abs(t-m) + sqrt((t-aa)*(t-bb)))/2)
def Urho(t): return sum(c[j]*Uw(a[j], b[j], t) for j in range(16))
def V(t):
    if t == 0: return -12*al*log(al) - 2 + 12*al
    return log(1+t) - 6*al*log(t+al**2) - 2 + 12*al + 2*sqrt(t)*(pi + atan(1/sqrt(t)) - 6*atan(al/sqrt(t)))
qm = mpf(59205077)/10**10; qp = mpf(59205079)/10**10
# check V' sign at q-, q+ : Phi'(y) = 2(pi + atan(1/y) - 6 atan(al/y)), y = sqrt t
Phip = lambda y: 2*(pi + atan(1/y) - 6*atan(al/y))
print("Phi'(sqrt q-) =", Phip(sqrt(qm)), " Phi'(sqrt q+) =", Phip(sqrt(qp)))
Vstar = log(1+qm) - 6*al*log(qp+al**2) - 2 + 12*al + 2*sqrt(qp)*(pi + atan(1/sqrt(qp)) - 6*atan(al/sqrt(qm)))
print("V* =", Vstar, " V(q-) =", V(qm), " V(q+) =", V(qp))
# partition points
A = [mpf(0)] + [a[16-j] for j in range(1,17)] + [qm, qp] + [b[j-1] for j in range(1,17)] + [mpf(2)]
assert len(A) == 36
def intervals_from_row(j, d, ks):
    return [(A[j] + (A[j+1]-A[j])*mpf(k)/2**d, A[j] + (A[j+1]-A[j])*mpf(k+1)/2**d) for k in ks]
rows = """0 1 0
0 2 2,3
1 0 0
2 0 0
3 0 0
4 0 0
5 0 0
6 0 0
7 0 0
8 0 0
9 1 0,1
10 1 0,1
11 1 0,1
12 1 0
12 2 2,3
13 2 0-3
14 2 0-3
15 1 0
15 2 2,3
16 0 0
17 0 0
18 0 0
19 1 1
19 3 0;2,3
19 4 2,3
20 2 3
20 3 4,5
20 4 0,1;6,7
20 5 4-11
21 2 3
21 3 5
21 4 0;7-9
21 5 2-4;10-13
21 6 10-19
22 3 5-7
22 4 0;8,9
22 5 2,3;12-15
22 6 8-23
23 3 6,7
23 4 9-11
23 5 0-2;14-17
23 6 6-13;19-27
23 7 28-37
24 3 6,7
24 4 10,11
24 5 0-2;15-19
24 6 6-11;22-29
24 7 24-43
25 3 7
25 4 10-13
25 5 0-2;16-19
25 6 6-11;24-31
25 7 24-47
26 3 7
26 4 11-13
26 5 0-2;17-21
26 6 6-11;25-33
26 7 24-49
27 4 11-15
27 5 0-2;17-21
27 6 6-11;26-33
27 7 24-51
28 4 12-15
28 5 0-2;18-23
28 6 6-11;27-35
28 7 24-53
29 4 13-15
29 5 0-2;19-25
29 6 6-12;27-37
29 7 26-53
30 4 13-15
30 5 0-2;20-25
30 6 6-14;26-39
30 7 30-51
31 4 14,15
31 5 0-2;20-27
31 6 6-39
32 4 15
32 5 0-4;19-29
32 6 10-37
33 4 0;15
33 5 2-29
34 2 2,3
34 3 3
34 4 3-5
34 5 4,5
34 6 5-7
34 7 6-9
34 8 7-11
34 9 5-13
34 10 0-9"""
def parse_ks(s):
    ks = []
    for part in s.split(';'):
        for piece in part.split(','):
            if '-' in piece:
                lo, hi = piece.split('-'); ks += list(range(int(lo), int(hi)+1))
            else: ks.append(int(piece))
    return ks
ivs = []
for line in rows.splitlines():
    j, d, ks = line.split(' ', 2)
    ivs += intervals_from_row(int(j), int(d), parse_ks(ks))
print("number of intervals:", len(ivs))
# check partition of [0,2]
ivs_sorted = sorted(ivs)
ok = ivs_sorted[0][0] == 0 and ivs_sorted[-1][1] == 2 and all(abs(ivs_sorted[i][1]-ivs_sorted[i+1][0]) < mpf(10)**-25 for i in range(len(ivs_sorted)-1))
print("partition of [0,2]:", ok)
worst = mpf(-100)
for (l, r) in ivs:
    if r <= qm: Vlow = V(r)
    elif l >= qp: Vlow = V(l)
    else: Vlow = Vstar
    B = 2*max(Urho(l), Urho(r)) - Vlow
    worst = max(worst, B)
print("max B(l,r) over Table 2 =", worst, "  paper bound: -6.645002 ; M0 =", M0)
# (6.8) for t >= 2: 2U^rho(t) - V(t) <= 13/10 log t + 6 al^3/t - 2 pi sqrt t, decreasing, value at 2 < M0
f68 = lambda t: mpf(13)/10*log(t) + 6*al**3/t - 2*pi*sqrt(t)
print("(6.8) RHS at 2 =", f68(2), " 2U-V at 2 =", 2*Urho(mpf(2)) - V(mpf(2)))
# brute-force sample of 2U - V on (0, 2] and beyond
import random
random.seed(3)
mx = mpf(-100); argmx = None
for _ in range(20000):
    t = mpf(random.random())*2
    v = 2*Urho(t) - V(t)
    if v > mx: mx, argmx = v, t
print("sampled max of 2U-V on (0,2):", mx, "at t =", argmx)
