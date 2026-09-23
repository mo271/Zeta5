# Zeta5

Lean 4 / Mathlib project around the statement

```lean
theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x
```

following the preprint [ζ(5) is irrational](https://zenodo.org/records/22826419). (A. Fauzan, 17 September 2026).

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`). The prime number theorem
`θ ~ id` comes from [PrimeNumberTheoremAnd](https://github.com/mo271/PrimeNumberTheoremAnd/tree/v4.33.1)
(the `v4.33.1` branch, pinned to commit `04d81b2a`), imported in `Apery/PNT.lean`.

License: Apache 2.0 (see `LICENSE`), as for Mathlib and PrimeNumberTheoremAnd.

## Status

**The formalisation is complete.** `irrational_five` is proved without `sorry`:

```
#print axioms Apery.irrational_five
-- [propext, Classical.choice, Quot.sound]
```

The two `sorry`s inside the `PrimeNumberTheoremAnd` dependency (`Wiener.lean`) are not reached.

**Deviation from the paper.** The normaliser is `mN n = ∏_{p ≤ 2h} p^{-L_p}` (`Apery/Norm.lean`),
where each `L_p` is one of the local bounds *proved here*:

* the small-prime bound (3.12), for `p · 400 ≤ K`;
* the inner-range bound with a water-filling allocation, for `K/400 < p ≤ K/3`;
* the outer-range bound with a full rank loss, for `p > K/3`.

This differs from the paper in three places:

* the rank loss is `r` rather than `min(r, z)` (Lemma 4.2), costing `9/640` in the constant;
* the cutoff is `M = 400` rather than 200;
* the valuation bounds are proved by direct class-wise partial fractions instead of the
  Tate-algebra functional.

Irrationality needs only `A_eff + U < 0`, not the paper's rate `139/5`. So `main_estimate` gives
`0 < Q_n(ζ(5)) < exp(-c n²)` with `c = -800(A_eff + U) > 0`, which suffices for the criterion.
Numerically, the constant these bounds achieve is `≈ 1.345`, below `A_eff = 1.36`, which is
below `-U = 1.36700`.

Proved parts of the paper: the degree formula (2.9); **Proposition 2.2 in full** (polynomial
moments from Euler's formula, pole moments via Hermite's formula at `s = 5`, partial fractions,
positivity of `Δ_K(ζ(5))`); **Section 6 in full** (Lemma 6.1 via Table 2, Lemma 6.2, the
configuration inequality (6.9), Andréief, (6.11)–(6.15), Proposition 6.3); Appendix A; Section 7;
**Sections 3–4 in the form above** (the bound (3.12) at every prime, the inner and outer local
bounds, unimodular class bases, Proposition 5.1 for `mN`).

| File | Content | Status |
|---|---|---|
| `Apery/Criterion.lean` | Irrationality criterion (paper §1.1): if for large `n` there is an integer polynomial `Q` of degree `≤ d n` with `0 < Q(ξ) ≤ ε n`, and `b^(d n) ε n → 0` for every positive integer `b`, then `ξ` is irrational. Also `b^(37n) exp(-139n²/5) → 0`. | proved |
| `Apery/Construction.lean` | Definitions of §2.1: `D_m`, the functional `μ_X` (2.2)–(2.3) via polynomial division and partial fractions, the Hankel matrix `G_K(X)` (2.4), `Δ_K = det G_K`, `S_K` (2.5), `F_K = S_K Δ_K`. | definitions |
| `Apery/Degree.lean` | (2.9): `deg Δ_K = deg F_K = h = 37 n`, via the affine entries and a weighted Vandermonde determinant. | proved |
| `Apery/Zeta5.lean` | `zeta5 : ℝ` and `riemannZeta 5 = ↑zeta5`. | proved |
| `Apery/Constants.lean` | `U`, `A*`, `A_M`, `A₂₀₀`; identity (5.20) and margin (7.2) by `norm_num`. | proved |
| `Apery/Stirling.lean` | `log m! ≤ m log m - m + (log m)/2 + 1`, `m log m - m ≤ log m!`, and `∑_{i<h} log (2i)! ≥ h² log 2h - 3h²/2 - 2h log 2h`. | proved |
| `Apery/Measure.lean` | `λ`, `α`, `C*` (6.3), `M₀`, Table 1 (the 16 arcsine components of `ρ`), `S_j`, `I(ρ)` by (A.2); `∑ c_j = λ`. | definitions + proved |
| `Apery/EnergyConst.lean` | (6.4): `λ M₀ - I(ρ) + C* ≤ U`, by certified rational lower bounds for 18 logarithms (artanh series with nonnegative terms + `Real.log_two_lt_d9`). The margin is `6.3·10⁻⁸`. | proved |
| `Apery/Weight.lean` | The weight `w` of (2.10): positivity, the bound `w(y) ≤ (32y+11)e^{-πy}`, measurability. | proved |
| `Apery/Moments.lean` | The polynomial moments `∫₀^∞ y^{2e} w(y) dy = μ(t^e)` with integrability, from the Gamma integral, term-wise integration and Euler's formula (`hasSum_zeta_nat`). | proved |
| `Apery/PartialFractions.lean` | `P(t)/D_K(t) = (P /ₘ D_K)(t) + ∑_j res_j/(t + j²)` for `t ≥ 0`, via Lagrange-type interpolation of the remainder. | proved |
| `Apery/Hermite.lean` | `∑ℓ⁴xˡ` in closed form; `F(y) = 1/(e^{2πy}-1)` and its derivatives to order 4 with `w = y⁵F⁽⁴⁾/12`; `g(y) = y⁵/(12(y²+a²))` and its derivatives; the Mittag-Leffler expansion of `F` from Mathlib's `cot_series_rep`; `∫₀^∞ g⁽⁴⁾ = 1/2`. | proved |
| `Apery/HermiteIntegrals.lean` | `∫₀^∞ g⁽⁴⁾(y)/y dy = π/a` and `∫₀^∞ g⁽⁴⁾(y) y/(y²+n²) dy = πa⁴/(a+n)⁵`, via explicit antiderivatives (rational part + arctan terms) verified by differentiation. | proved |
| `Apery/HermiteIBP.lean` | Uniform bounds on `F⁽ᵐ⁾` and `g⁽ʲ⁾`, integrability and vanishing boundary terms, and the four integrations by parts `∫₀^∞ g F⁽⁴⁾ = ∫₀^∞ g⁽⁴⁾ F`. | proved |
| `Apery/HermiteFormula.lean` | **Hermite's formula at `s = 5`**: `∫₀^∞ w(y)/(y²+j²) dy = j⁴(ζ(5) - H_j^{(5)}) - 1/4 + 1/(2j)`, by term-wise integration of the Mittag-Leffler expansion. | proved |
| `Apery/Positivity.lean` | The moment representation `moment_rep` (Proposition 2.2, proved from the above); `Δ_K(ζ(5)) > 0` (Gram matrix of a positive weight, `Matrix.PosDef.det_pos`). | proved |
| `Apery/Andreief.lean` | Andréief's identity `det(∫ fᵢ gⱼ dμ) = (1/n!) ∫ det(fᵢ(xⱼ)) det(gᵢ(xⱼ)) dμⁿ`. | proved |
| `Apery/DetIntegral.lean` | (6.10): `Δ_K(ζ(5)) = (1/h!) ∫_{(0,∞)^h} det V(y)² ∏ν(yᵢ) dy` with `V` the Vandermonde matrix of the `yᵢ²`. | proved |
| `Apery/Energy.lean` | The external field `V` (6.1); the bound `w(y) ≤ (1/π)(1+2πy)⁵e^{-2πy}`; both directions of the sum–integral comparison (6.12); `∫₀^∞(1+2πy)⁵e^{-y/K}dy ≤ C K⁶`; a.e. configurations have positive, pairwise distinct coordinates. | proved |
| `Apery/PotentialV.lean` | The closed form (A.5) of `V`: `∫₀^c log(t+u²)du = c log(t+c²) - 2c + 2√t arctan(c/√t)`. | proved |
| `Apery/EnergyBound.lean` | The configuration inequality (6.9) as `energy_ineq` (from `EnergyFinal`); the pointwise bound for the integrand of (6.10) and its integration, giving (6.14) as `log_Δ_le'`. | proved |
| `Apery/Potential.lean`, `Apery/TableCheck.lean`, `Apery/Table/*.lean` | Lemma 6.1: the potential `Uρ` of the arcsine measure (closed form (A.1)), monotonicity of `Uρ` and `V`, the reduction of (6.2) to endpoint checks, the certified endpoint bounds on all 684 intervals of Table 2 (generated, ~110k lines), the tail `t ≥ 2` via (6.8), and `potential_ineq : 2Uρ(t) - V(t) ≤ M₀` for all `t > 0`. | proved |
| `Apery/Gaussian.lean`, `Apery/ZeroMass.lean`, `Apery/Kernel.lean`, `Apery/EnergyLimit.lean` | Lemma 6.2 (zero-mass logarithmic energy) for finite families of parametrised curves with real weights: Gaussian positivity for the truncated kernel `L_{a,b}`, the limit `L_{a,b} → log` by dominated convergence, `energy_log_nonpos`. | proved |
| `Apery/CircleAtoms.lean`, `Apery/ArcsineAtoms.lean`, `Apery/ArcsinePotential.lean`, `Apery/EnergyAtoms.lean` | The circle and arcsine atoms: circle integrals of `log‖·-a‖` (from Mathlib's circle-average identity), the factorisation `z - (m + r cos θ) = -(r/2w)(w-q₁)(w-q₂)`, the potential formula (A.1) as `arc_potential_real`, the Hölder-1/2 estimate for the potential, integrability on the torus, and Lemma 6.2 applied to a configuration (`atom_energy_nonpos`). | proved |
| `Apery/EnergyBlocks.lean`, `Apery/EnergyRaw.lean`, `Apery/EnergyFinal.lean` | The four blocks of the atom energy (circle self-energy `(2π)² log ε`, circle–circle `≥ (2π)² log|tᵢ-tⱼ|`, circle–arcsine `≤ (2π)²(Uω(tᵢ) + error)`, arcsine–arcsine `≥ (2π)² I(ρ)` via `∑ c_j c_k f(max j k) = ∑ (S_j² - S_{j-1}²) f_j`), the raw inequality `energy_raw`, the error bound with `ε = K⁻⁶`, the pointwise bound (6.7), and **(6.9)** as `energy_ineq_final` with constants `(λM₀ - I(ρ))K² + 5h + 6h log K`. | proved |
| `Apery/RealBound.lean` | (6.14) as `log_Δ_le` (from `EnergyBound`), (6.15) as `log_S_le` (proved), and Proposition 6.3 (`real_bound'`) from `Δ_pos`, `log_Δ_le`, `energy_const`, `log_S_le` (proved). | proved |
| `Apery/Arith/Val.lean`, `IntPoly.lean`, `BinomBasis.lean`, `TauBound.lean`, `PoleFun.lean` | Valuations `VG` on `ℚ` and Gauss valuations `GV` on `ℚ[X]`, the weighted determinant bound `det_GV`; the Bernoulli functional, the binomial basis, the bound (3.9) (`tau_bound`); the functional `τ_X` on rational functions with integer poles. | proved |
| `Apery/Arith/DirectPoly.lean`, `DirectBound.lean` | The **direct entry bound** `tauX_direct`: `v_p^G(τ_X(g)) ≥ min_c(e_c − ℓ_c) − 4`, replacing the paper's Tate-algebra functional and distribution formula (Lemmas 3.1–3.2) by class-wise partial fractions. | proved |
| `Apery/Arith/Pullback.lean`, `BasisChange.lean`, `Unimodular.lean` | The pullback identity (3.1) `μX_eq_tauX`; linearity of `μ_X` and `det_basis_change` (`det[μ_X(D_N⁶E_aE_b)] = det(C)²Δ_K`); unimodularity of the class bases by CRT over `𝔽_p` (`coeffMat_det_unit`). | proved |
| `Apery/Arith/TEntry.lean`, `ClassFrame.lean`, `ClassCount.lean`, `InnerWeights.lean` | **Inner range** (Prop. 4.1 analogue): the class framework `class_frame` (valid weights `w` give `v_p^G(Δ_K) ≥ 2∑w`), the class counts, and `inner_bound_cap`: for any allocation `L` of the `37n` rows to the classes with `∑L = 37n` satisfying the zero-class condition, `v_p^G(Δ_K) ≥ 2∑ wcap`. | proved |
| `Apery/Arith/MomentVal.lean`, `LowRank.lean`, `OuterFrame.lean` | **Outer range framework**: `p`-integrality of the moments below `2p − 3` (von Staudt–Clausen), the low-rank correction of the high moments, and the Schur-complement bound `outer_frame`: `v_p^G(Δ_K) ≥ 2∑w − r` with `r = 37n − ((2p+22n−3) − (37n−1))`. | proved |
| `Apery/Arith/PoleVal.lean`, `OuterEntry.lean`, `OuterBasis.lean`, `OuterEntries.lean`, `OuterEntryMain.lean` | **Outer range entries** (Prop. 4.3 analogue): valuations of the pole values `μ_X(1/(t+j²))` (including the pairing `j, p−j` via `H^{(5)}` congruences, `pair_GV`); the class basis `rootsO` and its reduction mod `p`; the residue bounds per class; the three cases (both rows below the big-pole count, one row above it, the zero class); `outer_entry` and **`outer_bound`**: for `7 ≤ p`, `3n < p`, `40n < 3p`, `v_p^G(Δ_K) ≥ 2∑_c ∑_{i<Lo(c)} wO(c,i) − r`. | proved |
| `Apery/Normalization.lean` | The paper's definitions of `L_p(K, M)`, `γ_p^in`, `γ_p^out`, `m_{K,M}` (5.1)–(5.2), kept for reference; `vS`. | definitions |
| `Apery/Arith/SmallPrime*.lean` | **The bound (3.12)** at every prime (`small_prime_bound`): integer values of binomial polynomials, the window lemma (values at `d+1` consecutive integers control all integers), Kummer's bound, the residue products at `±1..±K`, the analogue of Lemma 3.3 without the paper's ball analysis (`crude_tauX`), and the basis `q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!` with `q_i(-z²) = C(z+i,2i) + C(z+i-1,2i)`. | proved |
| `Apery/Arith/InnerAlloc.lean` | The inner-range allocation by water filling: the largest feasible level `kf`, validity (zero-class condition), `∑ wcap ≥ Φ(kf) - B₀`, and concavity `Φ(kf) ≥ Φ(k) - (k - klo) L₀/2`. | proved |
| `Apery/Norm.lean` | The normaliser `mN` actually used: `Lp n p` is the small-prime, inner or outer bound (falling back to (3.12) when side conditions fail); validity `GV_F_Lp`, and **integrality** `integral_mN : ∃ Q : ℤ[X], Q.map _ = C (mN n) * F n` for `n ≥ 1`. | proved |
| `Apery/Growth/ClassSum.lean`, `ClassData.lean` | Class sums `∑_c h(a_c, a'_c)` as nine interval counts, each within `5/2` of `p` times its continuous limit (`class_sum_approx`); `SX p X c = 2⌊X/p⌋ + a_c`; Legendre-type bounds and the layer-cake bound for `v_p(S_K)`. | proved |
| `Apery/Growth/InnerPrime.lean` | Inner range, discrete form (`inner_Lp_le`): `-L_p ≤ -2hq + 12hq' + 2T(h) - hk + 2∑_c ψ(k, β_c) + O(1)` for every admissible level `k`, including the verification of the inner side conditions for large `n`. | proved |
| `Apery/Growth/TailPrime.lean` | Inner range, symbolic form (`tail_Lp_le`): `-L_p ≤ p (x F(x) + 27/16) + O(1)`, `F(x) = 4λ + 2λ{x} - 12λ{αx}`, via `ψ(t) ≤ (t+1)²/8` and a Popoviciu variance bound. | proved |
| `Apery/Growth/TablePrime.lean` | Inner range, exact continuous form (`table_Lp_le`): `-L_p ≤ p Ê_in(K/p, k) + O(1)`. Numerically `min_k Ê_in = R(x)` of (5.6), and its 125 linear pieces on `[3, 20]` integrate to exactly (5.18). | proved |
| `Apery/Growth/OuterPrime.lean` | Outer range (`outer_Lp_le`): class counts via `SX`, the per-class weight sums, the zero class, the rank loss, `-L_p ≤ p Ê_out(K/p) + O(1)`; the 13 linear pieces of `Ê_out` integrate to exactly `127751/96000 + 9/640`. | proved |
| `Apery/Growth/TableGen.lean`, `InnerTable.lean`, `InnerSum.lean`, `OuterTable.lean`, `TableIntegrals.lean` | The piece tables (generated by `scripts/growth/`): 125 inner pieces and 13 outer pieces, each `Ê(x) = a_i x + b_i` proved, and their exact integrals `(5.18)` and `129101/96000`. | proved |
| `Apery/Growth/TailIntegral.lean` | Integration by parts on `[20, 400]` over 1140 pieces with `P`, `C` continuous across breakpoints: `∑ ∫ (xF + 27/16)/x³ ≤ -6843153/128000000`. | proved |
| `Apery/Growth/Assembly*.lean`, `PieceIdx.lean`, `Constants.lean` | `log m_K = ∑ c(p)(-L_p)`, the four prime ranges, uniform bounds on the additive constants, the piecewise prime-sum limits (`psum_piecewise_le`). | proved |
| `Apery/Growth.lean` | `growth_mN`: `log mN ≤ (A_eff + ε) K²` eventually; the total constant is `1.3480… < A_eff = 1.36`. | proved |
| `Apery/Legendre.lean` | (5.3): `v_p(S_K) = 2h v_p(K!) - 12h v_p(N!) - 2∑ v_p((2i)!) + (h-1) v_p(4)` (`vS_eq`). | proved |
| `Apery/PrimeSum.lean` | Weighted prime sums: Abel summation `∑_{a<p≤b} p log p = bθ(b) - aθ(a) - ∫θ` and, from the prime number theorem, `K⁻² ∑_{K/d<p≤K/c} p log p → (1/c² - 1/d²)/2` (`wsum_tendsto`). | proved |
| `Apery/PrimeSumStep.lean` | Weighted prime sums `psum f a b K = ∑_{K/b<p≤K/a} p f(K/p) log p`: splitting over a partition, upper Darboux bound by step sums, and its limit (`psum_eventually_le`). | proved |
| `Apery/PrimeSumIntegral.lean` | `K⁻² ∑_{K/b<p≤K/a} p f(K/p) log p ≤ ∫_a^b f(x)/x³ dx + ε` for all large `K`, for `f` Lipschitz on `[a, b]` (`psum_le_integral`) and for piecewise Lipschitz `f` (`psum_piecewise_le`). | proved |
| `Apery/MainEstimate.lean` | `normalization` from `integral_mN` and `growth_mN`; Theorem 2.1 in the form `main_estimate` (decay `exp(-c n²)` with `c = -800(A_eff+U) > 0`) from `degree_F`, `real_bound`, `normalization`. | proved (modulo `growth_mN`) |
| `Apery/Main.lean` | `irrational_zeta5` and `irrational_five`. | proved |
| `Apery/PNT.lean` | The prime number theorem `θ ~ id` (`theta_asymptotic`), from the `PrimeNumberTheoremAnd` dependency. | imported |

How `growth_mN` is assembled. `log m_K = ∑_{p ≤ 2h} (-L_p) log p` is split into four prime
ranges:

| Range, with `x = K/p` | Per-prime bound | Contribution to `K⁻² log m_K` |
|---|---|---|
| `p ≤ K/400` | `-L_p = 6h⌊log_p 200n⌋ + h v_p(24)` | `6λ/400 = 0.013875` (PNT) |
| `3 ≤ x ≤ 20` | `table_Lp_le` | `(5.18) = 0.042788…` |
| `20 ≤ x ≤ 400` | `tail_Lp_le` | `≤ -0.053462…` |
| `20/37 ≤ x < 3` | `outer_Lp_le` | `129101/96000 = 1.344802…` |

The total is `1.348003… < A_eff = 1.36 < -U = 1.36700`.

## Numerical checks of the paper (not part of the Lean development)

Exact computations of `Δ_K(X) ∈ ℚ[X]` for `K = 40, 80, ..., 240` (python-flint), with
`P_K := Δ_K / content(Δ_K)` the primitive integer polynomial:

| n | K | log F_K(ζ5) / K² | −log content(F_K) / K² | log P_K(ζ5) | log P_K(ζ5) / n² |
|---|---|---|---|---|---|
| 1 | 40 | −1.276 | 1.110 | −265 | −265 |
| 2 | 80 | −1.329 | 1.199 | −833 | −208 |
| 3 | 120 | −1.348 | 1.223 | −1804 | −200 |
| 4 | 160 | −1.357 | 1.230 | −3247 | −203 |
| 5 | 200 | −1.363 | 1.251 | −4479 | −179 |
| 6 | 240 | −1.367 | 1.251 | −6669 | −185 |

The paper's asymptotic constants are `U = −1.36700` (real side) and `A_200 = 1.34960`
(normalisation), giving the claimed `−139/5 = −27.8` per `n²`. The exact rational data of
Appendix B (the integrals (5.18) and (5.10), Tables 3 and 4, and `A*`) were recomputed from the
paper's definitions and agree exactly (`scripts/appendixB.py`); the constants of Appendix A.4
(`I(ρ)`, `C*`, and the margin `6.45·10⁻⁸` in (6.4)) were recomputed to 40 digits and agree; the
potential inequality (6.2) of Lemma 6.1 was recomputed over the 684 intervals of Table 2
(`scripts/lemma61.py`) and holds with the stated margin. Also verified exactly: the
leading-coefficient formula (2.9), the moment formulas (2.2)/(2.3) by numerical integration,
the valuation bound (3.12) at every prime, integrality at primes `p > K`, and the outer-range
bound `γ_p^out` of (4.14)/Proposition 4.3 at every admissible prime (it is attained exactly at
most of them).
