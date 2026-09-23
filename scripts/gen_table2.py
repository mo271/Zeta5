#!/usr/bin/env python3
"""Generate Lean certificates for the potential inequality (6.2) over the Table 2 partition.
Usage: gen_table2.py [--subset N] ; writes Apery/Table2/*.lean"""
import sys, math
from fractions import Fraction as Fr
from mpmath import mp, mpf, sqrt as msqrt, atan as matan, log as mlog, pi as mpi
mp.dps = 50
OUT = '/home/moritz/Apery/Apery/Table2'
T = [(3906748086,8992695531,10515596180),(2312248264,15340997855,29471737793),(1402286665,25730180724,42934365099),(881725356,41909578246,58204231966),(578197906,65851089563,69037621310),(396324613,99481037884,78873099189),(283911191,144325727458,84856120711),(212206188,201105762729,88396082127),(165097686,269345996903,88303382125),(133347132,347089554156,85472321255),(111522114,430806704415,78899184238),(96349355,515561896511,70353471918),(85815639,595448778546,58838976615),(78667711,664241383483,44421321106),(74129565,716160577112,30462865791),(71741310,746637295669,5959622577)]
D = 10**12
A = [Fr(x[0], D) for x in T]; B = [Fr(x[1], D) for x in T]; C = [Fr(x[2], D) for x in T]
AL = Fr(3, 40); M0 = Fr(-1329, 200)
QM = Fr(59205077, 10**10); QP = Fr(59205079, 10**10)
LOG2_LO = Fr('0.6931471803'); LOG2_HI = Fr('0.6931471808')
PI_LO = Fr('3.14159265358979323846'); PI_HI = Fr('3.14159265358979323847')

def lean_rat(q):
    q = Fr(q)
    if q.denominator == 1: return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"

# ---------- certificate primitives (return (lean_proof_term_or_tactic_block, bound)) ----------
def log_upper(y, m=11):
    """certified rational u with log y <= u, y > 0 rational. Returns (k, u, expr_fraction)."""
    y = Fr(y); k = 0
    while 2**k * y < 1: k += 1
    r = 2**k * y; x = (r - 1) / (r + 1)
    expr = 2 * sum(Fr(1, 2*j+1) * x**(2*j+1) for j in range(m)) + 2 * x**(2*m+1) / ((2*m+1) * (1 - x*x)) - k * LOG2_LO
    u = Fr(math.ceil(expr * 10**14), 10**14)
    return k, u
def log_lower(y, m=11):
    y = Fr(y); k = 0
    while 2**k * y < 1: k += 1
    r = 2**k * y; x = (r - 1) / (r + 1)
    expr = 2 * sum(Fr(1, 2*j+1) * x**(2*j+1) for j in range(m)) - k * LOG2_HI
    l = Fr(math.floor(expr * 10**14), 10**14)
    return k, l
def sqrt_upper(q):
    q = Fr(q)
    s = Fr(math.ceil(msqrt(mpf(q.numerator)/q.denominator) * 10**14), 10**14)
    while s*s < q: s += Fr(1, 10**14)
    return s
def sqrt_lower(q):
    q = Fr(q)
    s = Fr(math.floor(msqrt(mpf(q.numerator)/q.denominator) * 10**14), 10**14)
    while s*s > q: s -= Fr(1, 10**14)
    return max(s, Fr(0))
def series_atan_lower(x, kk):   # sum over range (2kk) of alternating terms
    x = Fr(x); return sum((-1)**i * x**(2*i+1) / (2*i+1) for i in range(2*kk))
def series_atan_upper(x, kk):   # range (2kk+1)
    x = Fr(x); return sum((-1)**i * x**(2*i+1) / (2*i+1) for i in range(2*kk+1))

class Emitter:
    def __init__(self): self.lines = []; self.n = 0
    def fresh(self, base):
        self.n += 1; return f"{base}{self.n}"
    def emit(self, s): self.lines.append("  " + s)

def emit_log_upper(E, arg_lean, y):
    """emit `have h : Real.log arg_lean ≤ u`; return (name, u)."""
    k, u = log_upper(y)
    h = E.fresh("hL")
    E.emit(f"have {h} : Real.log {arg_lean} ≤ {lean_rat(u)} := by")
    E.emit(f"  refine le_trans (log_le_of_pow_two_upper (by norm_num) {k} 11 (by norm_num)) ?_")
    E.emit(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num")
    return h, u
def emit_log_lower(E, arg_lean, y):
    k, l = log_lower(y)
    h = E.fresh("hL")
    E.emit(f"have {h} : {lean_rat(l)} ≤ Real.log {arg_lean} := by")
    E.emit(f"  refine le_trans ?_ (log_ge_of_pow_two (by norm_num) {k} 11 (by norm_num))")
    E.emit(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num")
    return h, l
def emit_atan_lower(E, x):
    """emit `have h : q ≤ Real.arctan x_lean` for rational x > 0; return (name, q)."""
    x = Fr(x); h = E.fresh("hA")
    if x > 1:
        # arctan x = π/2 - arctan (1/x)
        hu, qu = emit_atan_upper(E, 1/x)
        q = PI_LO/2 - qu
        E.emit(f"have {h} : {lean_rat(q)} ≤ Real.arctan {lean_rat(x)} := by")
        E.emit(f"  rw [arctan_eq_pi_div_two_sub (by norm_num)]")
        E.emit(f"  have := Real.pi_gt_d20")
        E.emit(f"  have e : (1 : ℝ) / {lean_rat(x)} = {lean_rat(1/x)} := by norm_num")
        E.emit(f"  rw [e]; linarith [{hu}]")
        return h, q
    if x > Fr(1, 2):
        w = sqrt_upper(1 + x*x); y = x / (1 + w)
        hy, qy = emit_atan_lower(E, y)
        q = 2 * qy
        E.emit(f"have {h} : {lean_rat(q)} ≤ Real.arctan {lean_rat(x)} := by")
        E.emit(f"  have hw : Real.sqrt (1 + {lean_rat(x)} ^ 2) ≤ {lean_rat(w)} := sqrt_le_of_sq_le (by norm_num) (by norm_num)")
        E.emit(f"  have := arctan_ge_half (by norm_num) hw")
        E.emit(f"  have e : {lean_rat(x)} / (1 + {lean_rat(w)}) = {lean_rat(y)} := by norm_num")
        E.emit(f"  rw [e] at this; linarith [{hy}]")
        return h, q
    kk = 8
    q = Fr(math.floor(series_atan_lower(x, kk) * 10**15), 10**15)
    E.emit(f"have {h} : {lean_rat(q)} ≤ Real.arctan {lean_rat(x)} := by")
    E.emit(f"  refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) {kk})")
    E.emit(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num")
    return h, q
def emit_atan_upper(E, x):
    x = Fr(x); h = E.fresh("hA")
    if x > 1:
        hl, ql = emit_atan_lower(E, 1/x)
        q = PI_HI/2 - ql
        E.emit(f"have {h} : Real.arctan {lean_rat(x)} ≤ {lean_rat(q)} := by")
        E.emit(f"  rw [arctan_eq_pi_div_two_sub (by norm_num)]")
        E.emit(f"  have := Real.pi_lt_d20")
        E.emit(f"  have e : (1 : ℝ) / {lean_rat(x)} = {lean_rat(1/x)} := by norm_num")
        E.emit(f"  rw [e]; linarith [{hl}]")
        return h, q
    if x > Fr(1, 2):
        w = sqrt_lower(1 + x*x); y = x / (1 + w)
        hy, qy = emit_atan_upper(E, y)
        q = 2 * qy
        E.emit(f"have {h} : Real.arctan {lean_rat(x)} ≤ {lean_rat(q)} := by")
        E.emit(f"  have hw : {lean_rat(w)} ≤ Real.sqrt (1 + {lean_rat(x)} ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)")
        E.emit(f"  have := arctan_le_half (by norm_num) (by norm_num) hw")
        E.emit(f"  have e : {lean_rat(x)} / (1 + {lean_rat(w)}) = {lean_rat(y)} := by norm_num")
        E.emit(f"  rw [e] at this; linarith [{hy}]")
        return h, q
    kk = 8
    q = Fr(math.ceil(series_atan_upper(x, kk) * 10**15), 10**15)
    E.emit(f"have {h} : Real.arctan {lean_rat(x)} ≤ {lean_rat(q)} := by")
    E.emit(f"  refine le_trans (arctan_le_partial (by norm_num) (by norm_num) {kk}) ?_")
    E.emit(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num")
    return h, q

# ---------- U point lemma ----------
def U_bound_terms(p):
    """for each j: (case, s, u) with Uω(a_j,b_j,p) ≤ u."""
    res = []
    for j in range(16):
        a, b = A[j], B[j]; m = (a + b) / 2
        if a <= p <= b:
            arg = (b - a) / 4; k, u = log_upper(arg); res.append(('in', None, arg, u))
        elif p >= b:
            s = sqrt_upper((p - a) * (p - b)); arg = (p - m + s) / 2; k, u = log_upper(arg); res.append(('right', s, arg, u))
        else:
            s = sqrt_upper((p - a) * (p - b)); arg = (m - p + s) / 2; k, u = log_upper(arg); res.append(('left', s, arg, u))
    return res

def emit_U_lemma(name, p):
    E = Emitter(); terms = U_bound_terms(p)
    UB = sum(C[j] * terms[j][3] for j in range(16))
    E.lines.append(f"lemma {name} : Uρ {lean_rat(p)} ≤ {lean_rat(UB)} := by")
    E.emit("rw [Uρ_eq]")
    E.emit("rw [" + ", ".join(f"aρ_{j+1}, bρ_{j+1}, cρ_{j+1}" for j in range(16)) + "]")
    hs = []
    for j in range(16):
        case, s, arg, u = terms[j]; a, b = A[j], B[j]
        if case == 'in':
            argl = f"(({lean_rat(b)} - {lean_rat(a)}) / 4)"
        elif case == 'right':
            argl = f"(({lean_rat(p)} - ({lean_rat(a)} + {lean_rat(b)}) / 2 + {lean_rat(s)}) / 2)"
        else:
            argl = f"((({lean_rat(a)} + {lean_rat(b)}) / 2 - {lean_rat(p)} + {lean_rat(s)}) / 2)"
        hl, _ = emit_log_upper(E, argl, arg)
        h = E.fresh("hU")
        if case == 'in':
            E.emit(f"have {h} : Uω {lean_rat(a)} {lean_rat(b)} {lean_rat(p)} ≤ {lean_rat(u)} := Uω_le_inside (by norm_num) (by norm_num) {hl}")
        elif case == 'right':
            E.emit(f"have {h} : Uω {lean_rat(a)} {lean_rat(b)} {lean_rat(p)} ≤ {lean_rat(u)} := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) {hl}")
        else:
            E.emit(f"have {h} : Uω {lean_rat(a)} {lean_rat(b)} {lean_rat(p)} ≤ {lean_rat(u)} := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) {hl}")
        hs.append(h)
    E.emit("linarith [" + ", ".join(hs) + "]")
    return "\n".join(E.lines), UB

# ---------- V point lemma ----------
def emit_V_lemma(name, p):
    E = Emitter()
    slo, shi = sqrt_lower(p), sqrt_upper(p)
    if slo <= 0: slo = Fr(1, 10**14)  # p > 0 so sqrt > 0; ensure positivity (slo^2 <= p still needed)
    while slo * slo > p: slo -= Fr(1, 10**15)
    k1, l1 = log_lower(1 + p); k2, l2 = log_upper(p + AL*AL)
    # arctan(1/√p) ≥ arctan(1/shi) ≥ A1 ; arctan(α/√p) ≤ arctan(α/slo) ≤ A2
    E.lines.append(None)  # placeholder for header
    hl1, _ = emit_log_lower(E, f"(1 + {lean_rat(p)})", 1 + p)
    hl2, _ = emit_log_upper(E, f"({lean_rat(p)} + (3 / 40) ^ 2)", p + AL*AL)
    hA1, A1 = emit_atan_lower(E, 1/shi)
    hA2, A2 = emit_atan_upper(E, AL/slo)
    Plo = PI_LO + A1 - 6*A2
    pos = Plo >= 0
    sfac = slo if pos else shi
    v = l1 - 6*AL*l2 - 2 + 12*AL + 2*sfac*Plo
    hdr = f"lemma {name} : {lean_rat(v)} ≤ Vfield {lean_rat(p)} := by"
    E.lines[0] = hdr
    body = [
      f"  have hp : (0 : ℝ) < {lean_rat(p)} := by norm_num",
      f"  have hs1 : {lean_rat(slo)} ≤ Real.sqrt {lean_rat(p)} := le_sqrt_of_sq_le (by norm_num) (by norm_num)",
      f"  have hs2 : Real.sqrt {lean_rat(p)} ≤ {lean_rat(shi)} := sqrt_le_of_sq_le (by norm_num) (by norm_num)",
      f"  have e1 : (1 : ℝ) / {lean_rat(shi)} = {lean_rat(1/shi)} := by norm_num",
      f"  have e2 : (3 / 40 : ℝ) / {lean_rat(slo)} = {lean_rat(AL/slo)} := by norm_num",
    ]
    lemma = "Vfield_ge_of_bounds_pos" if pos else "Vfield_ge_of_bounds_neg"
    tail = [
      f"  have hA1' : {lean_rat(A1)} ≤ Real.arctan (1 / {lean_rat(shi)}) := by rw [e1]; exact {hA1}",
      f"  have hA2' : Real.arctan ((3 / 40) / {lean_rat(slo)}) ≤ {lean_rat(A2)} := by rw [e2]; exact {hA2}",
      f"  have := {lemma} hp (by norm_num) hs1 hs2 {hl1} {hl2} hA1' hA2' (by norm_num)",
      f"  linarith",
    ]
    return "\n".join([E.lines[0]] + body + E.lines[1:] + tail), v

# ---------- partition ----------
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
Apts = [Fr(0)] + [A[16-j] for j in range(1,17)] + [QM, QP] + [B[j-1] for j in range(1,17)] + [Fr(2)]
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
    j, d, ks = line.split(' ', 2); j = int(j); d = int(d)
    for k in parse_ks(ks):
        ivs.append((Apts[j] + (Apts[j+1]-Apts[j])*Fr(k, 2**d), Apts[j] + (Apts[j+1]-Apts[j])*Fr(k+1, 2**d)))
ivs.sort()
pts = [ivs[0][0]] + [r for (l, r) in ivs]
assert all(ivs[i][1] == ivs[i+1][0] for i in range(len(ivs)-1)) and pts[0] == 0 and pts[-1] == 2
a1, b1 = A[0], B[0]
assert a1 in pts and b1 in pts and QM in pts and QP in pts

def main():
    subset = None
    if len(sys.argv) > 2 and sys.argv[1] == '--subset': subset = int(sys.argv[2])
    N = len(ivs) if subset is None else subset
    # Data file
    data = ["import Apery.PotentialIneq", "", "namespace Apery", ""]
    for j in range(16):
        data.append(f"lemma aρ_{j+1} : aρ {j+1} = {lean_rat(A[j])} := by norm_num [aρ, table1]")
        data.append(f"lemma bρ_{j+1} : bρ {j+1} = {lean_rat(B[j])} := by norm_num [bρ, table1]")
        data.append(f"lemma cρ_{j+1} : cρ {j+1} = {lean_rat(C[j])} := by norm_num [cρ, table1]")
    data += ["", "/-- Template for a certified lower bound of `V` (parenthesis nonnegative). -/",
"""lemma Vfield_ge_of_bounds_pos {p slo shi l1 l2 A1 A2 : ℝ} (hp : 0 < p) (hslo : 0 < slo)
    (hs1 : slo ≤ Real.sqrt p) (hs2 : Real.sqrt p ≤ shi) (hl1 : l1 ≤ Real.log (1 + p))
    (hl2 : Real.log (p + (3 / 40) ^ 2) ≤ l2) (hA1 : A1 ≤ Real.arctan (1 / shi))
    (hA2 : Real.arctan ((3 / 40) / slo) ≤ A2)
    (hP : 0 ≤ 3.14159265358979323846 + A1 - 6 * A2) :
    l1 - 6 * (3 / 40) * l2 - 2 + 12 * (3 / 40) + 2 * slo * (3.14159265358979323846 + A1 - 6 * A2) ≤ Vfield p := by
  rw [Vfield_eq hp]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hshi : 0 < shi := hsp.trans_le hs2
  have hm1 : Real.arctan (1 / shi) ≤ Real.arctan (1 / Real.sqrt p) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsp hs2)
  have hm2 : Real.arctan ((3 / 40) / Real.sqrt p) ≤ Real.arctan ((3 / 40) / slo) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hslo hs1)
  have hpi := Real.pi_gt_d20
  have hPle : 3.14159265358979323846 + A1 - 6 * A2 ≤
      Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p) := by linarith
  have hprod : 2 * slo * (3.14159265358979323846 + A1 - 6 * A2) ≤
      2 * Real.sqrt p * (Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p)) :=
    mul_le_mul (by linarith) hPle hP (by positivity)
  have hl2' : 6 * (3 / 40) * Real.log (p + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * l2 :=
    mul_le_mul_of_nonneg_left hl2 (by norm_num)
  linarith""",
"", "/-- Template for a certified lower bound of `V` (parenthesis nonpositive). -/",
"""lemma Vfield_ge_of_bounds_neg {p slo shi l1 l2 A1 A2 : ℝ} (hp : 0 < p) (hslo : 0 < slo)
    (hs1 : slo ≤ Real.sqrt p) (hs2 : Real.sqrt p ≤ shi) (hl1 : l1 ≤ Real.log (1 + p))
    (hl2 : Real.log (p + (3 / 40) ^ 2) ≤ l2) (hA1 : A1 ≤ Real.arctan (1 / shi))
    (hA2 : Real.arctan ((3 / 40) / slo) ≤ A2)
    (hP : 3.14159265358979323846 + A1 - 6 * A2 ≤ 0) :
    l1 - 6 * (3 / 40) * l2 - 2 + 12 * (3 / 40) + 2 * shi * (3.14159265358979323846 + A1 - 6 * A2) ≤ Vfield p := by
  rw [Vfield_eq hp]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hshi : 0 < shi := hsp.trans_le hs2
  have hm1 : Real.arctan (1 / shi) ≤ Real.arctan (1 / Real.sqrt p) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsp hs2)
  have hm2 : Real.arctan ((3 / 40) / Real.sqrt p) ≤ Real.arctan ((3 / 40) / slo) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hslo hs1)
  have hpi := Real.pi_gt_d20
  have hPle : 3.14159265358979323846 + A1 - 6 * A2 ≤
      Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p) := by linarith
  have hprod : 2 * shi * (3.14159265358979323846 + A1 - 6 * A2) ≤
      2 * Real.sqrt p * (Real.pi + Real.arctan (1 / Real.sqrt p) - 6 * Real.arctan ((3 / 40) / Real.sqrt p)) := by
    calc 2 * shi * (3.14159265358979323846 + A1 - 6 * A2)
        ≤ 2 * Real.sqrt p * (3.14159265358979323846 + A1 - 6 * A2) :=
          mul_le_mul_of_nonpos_right (by linarith) hP
      _ ≤ _ := mul_le_mul_of_nonneg_left hPle (by positivity)
  have hl2' : 6 * (3 / 40) * Real.log (p + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * l2 :=
    mul_le_mul_of_nonneg_left hl2 (by norm_num)
  linarith""", "", "end Apery", ""]
    open(f"{OUT}/Data.lean", "w").write("\n".join(data))
    # points used
    used_pts = pts[:N+1]
    UB = {}
    CH = 40  # points per file
    nU = (len(used_pts) + CH - 1) // CH
    for c in range(nU):
        chunk = used_pts[c*CH:(c+1)*CH]
        lines = ["import Apery.Table2.Data", "", "set_option maxHeartbeats 4000000", "", "namespace Apery", ""]
        for i, p in enumerate(chunk):
            idx = c*CH + i
            txt, ub = emit_U_lemma(f"U_pt_{idx}", p); UB[idx] = ub
            lines += [txt, ""]
        lines += ["end Apery", ""]
        open(f"{OUT}/U{c:02d}.lean", "w").write("\n".join(lines))
    # intervals
    VB = {}
    nI = (N + CH - 1) // CH
    for c in range(nI):
        lo, hi = c*CH, min((c+1)*CH, N)
        imports = set()
        for k in range(lo, hi):
            imports.add(f"Apery.Table2.U{(k)//CH:02d}"); imports.add(f"Apery.Table2.U{(k+1)//CH:02d}")
        lines = [f"import {m}" for m in sorted(imports)] + ["", "set_option maxHeartbeats 4000000", "", "namespace Apery", ""]
        for k in range(lo, hi):
            l, r = ivs[k]
            # V lower bound
            if r <= QM:
                vname = f"V_pt_{k}"; txt, v = emit_V_lemma(vname, r); lines += [txt, ""]
                vcase = 'right'
            elif l >= QP:
                vname = f"V_pt_{k}"; txt, v = emit_V_lemma(vname, l); lines += [txt, ""]
                vcase = 'left'
            else:
                assert l == QM and r == QP
                vcase = 'star'; vname = None
                # certify Vstar >= v
                E = Emitter()
                slo_m, shi_p = sqrt_lower(QM), sqrt_upper(QP)
                k1, l1 = log_lower(1 + QM); k2, l2 = log_upper(QP + AL*AL)
                hl1, _ = emit_log_lower(E, f"(1 + qm)", 1 + QM)
                hl2, _ = emit_log_upper(E, f"(qp + (3 / 40) ^ 2)", QP + AL*AL)
                hA1, A1 = emit_atan_lower(E, 1/shi_p)
                hA2, A2 = emit_atan_upper(E, AL/slo_m)
                Plo = PI_LO + A1 - 6*A2
                assert Plo < 0
                v = l1 - 6*AL*l2 - 2 + 12*AL + 2*shi_p*Plo
                star = [f"lemma Vstar_ge : {lean_rat(v)} ≤ Vstar := by",
                        f"  unfold Vstar",
                        f"  have hs1 : {lean_rat(slo_m)} ≤ Real.sqrt qm := le_sqrt_of_sq_le (by norm_num) (by norm_num)",
                        f"  have hs2 : Real.sqrt qp ≤ {lean_rat(shi_p)} := sqrt_le_of_sq_le (by norm_num) (by norm_num)",
                        f"  have hsqp : 0 < Real.sqrt qp := sqrt_qp_pos",
                        f"  have e1 : (1 : ℝ) / {lean_rat(shi_p)} = {lean_rat(1/shi_p)} := by norm_num",
                        f"  have e2 : (3 / 40 : ℝ) / {lean_rat(slo_m)} = {lean_rat(AL/slo_m)} := by norm_num"] + E.lines + [
                        f"  have hm1 : Real.arctan (1 / {lean_rat(shi_p)}) ≤ Real.arctan (1 / Real.sqrt qp) := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsqp hs2)",
                        f"  have hm2 : Real.arctan ((3 / 40) / Real.sqrt qm) ≤ Real.arctan ((3 / 40) / {lean_rat(slo_m)}) := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1)",
                        f"  rw [e1] at hm1; rw [e2] at hm2",
                        f"  have hpi := Real.pi_gt_d20",
                        f"  have hPle : {lean_rat(Plo)} ≤ Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm) := by linarith [{hA1}, {hA2}]",
                        f"  have hprod : 2 * {lean_rat(shi_p)} * {lean_rat(Plo)} ≤ 2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm)) := by",
                        f"    calc 2 * {lean_rat(shi_p)} * {lean_rat(Plo)} ≤ 2 * Real.sqrt qp * {lean_rat(Plo)} := mul_le_mul_of_nonpos_right (by linarith) (by norm_num)",
                        f"      _ ≤ _ := mul_le_mul_of_nonneg_left hPle (by positivity)",
                        f"  have hl2' : 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * {lean_rat(l2)} := mul_le_mul_of_nonneg_left {hl2} (by norm_num)",
                        f"  linarith", ""]
                lines += star
            VB[k] = v
            # interval lemma
            ul, ur = UB[k], UB[k+1]
            if r <= a1: ucase, ub = 'anti', ul
            elif l >= b1: ucase, ub = 'mono', ur
            else:
                assert a1 <= l and r <= b1; ucase, ub = 'const', ul
            assert 2*ub - v <= M0, (k, float(2*ub - v))
            L = [f"lemma I_{k} : ∀ t : ℝ, {lean_rat(l)} < t → t ≤ {lean_rat(r)} → 2 * Uρ t - Vfield t ≤ M0 := by",
                 f"  intro t h1 h2",
                 f"  have hU : Uρ t ≤ {lean_rat(ub)} := by"]
            if ucase == 'anti':
                L += [f"    refine le_trans (Uρ_antitoneOn (show {lean_rat(l)} ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_{k}"]
            elif ucase == 'mono':
                L += [f"    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show {lean_rat(r)} ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_{k+1}"]
            else:
                L += [f"    have e1 := Uρ_of_mem (t := t) (by rw [aρ_1]; linarith) (by rw [bρ_1]; linarith)",
                      f"    have e2 := Uρ_of_mem (t := {lean_rat(l)}) (by rw [aρ_1]; norm_num) (by rw [bρ_1]; norm_num)",
                      f"    rw [e1, ← e2]; exact U_pt_{k}"]
            L += [f"  have hV : {lean_rat(v)} ≤ Vfield t := by"]
            if vcase == 'right':
                L += [f"    have hq : {lean_rat(r)} ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num",
                      f"    refine le_trans {vname} (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show {lean_rat(r)} ∈ Set.Ioc 0 qm from ⟨by norm_num, by show {lean_rat(r)} ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)"]
            elif vcase == 'left':
                L += [f"    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ {lean_rat(l)} := by norm_num",
                      f"    refine le_trans {vname} (Vfield_monotoneOn (show {lean_rat(l)} ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ {lean_rat(l)}; norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)"]
            else:
                L += [f"    exact le_trans Vstar_ge (Vfield_ge_Vstar h1.le h2)"]
            L += [f"  show _ ≤ -1329 / 200", f"  linarith", ""]
            lines += L
        lines += ["end Apery", ""]
        open(f"{OUT}/I{c:02d}.lean", "w").write("\n".join(lines))
    # assembly: binary split over intervals 0..N-1
    lines = [f"import Apery.Table2.I{c:02d}" for c in range(nI)] + ["", "namespace Apery", ""]
    def build(lo, hi):  # intervals lo..hi-1 ; returns lemma name proving ∀ t, p_lo < t → t ≤ p_hi → ...
        if hi - lo == 1:
            return f"I_{lo}"
        mid = (lo + hi) // 2
        name = f"J_{lo}_{hi}"
        left = build(lo, mid); right = build(mid, hi)
        lines.append(f"lemma {name} : ∀ t : ℝ, {lean_rat(pts[lo])} < t → t ≤ {lean_rat(pts[hi])} → 2 * Uρ t - Vfield t ≤ M0 := by")
        lines.append(f"  intro t h1 h2")
        lines.append(f"  rcases le_or_gt t {lean_rat(pts[mid])} with h | h")
        lines.append(f"  · exact {left} t h1 h")
        lines.append(f"  · exact {right} t h h2")
        lines.append("")
        return name
    top = build(0, N)
    lines += [f"theorem potential_ineq_le_two : ∀ t : ℝ, 0 < t → t ≤ {lean_rat(pts[N])} → 2 * Uρ t - Vfield t ≤ M0 := {top}", "", "end Apery", ""]
    open(f"{OUT}/All.lean", "w").write("\n".join(lines))
    print("generated:", N, "intervals,", len(used_pts), "points, files U:", nU, "I:", nI)
main()
