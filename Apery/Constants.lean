import Mathlib

/-!
# Numerical constants of the paper

`U` of (6.4), `A*` of (5.19), `A_M` of (5.20), the displayed value `A₂₀₀` of Appendix B.3,
the identity (5.20) at `M = 200` and the margin (7.2), both checked by `norm_num`.
-/

namespace Apery

/-- The constant `U` of Lemma 6.1 / (6.4). -/
def U : ℚ := -2733991 / 2000000

/-- The constant `A*` of (5.19). -/
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- `A_M` of (5.20), with `λ = 37/40`. -/
def A (M : ℚ) : ℚ := Astar + 7 * (37 / 40) / M - (2923 / 240 - 1 / 4) / M ^ 2 + 32 / M ^ 3

/-- The value `A₂₀₀` displayed in Appendix B.3. -/
def A200 : ℚ := 127125602969131786927559 / 94195881588024216000000

lemma A_200_eq : A 200 = A200 := by
  unfold A Astar A200; norm_num

/-- The rational margin (7.2): `-1600 (A₂₀₀ + U) > 139 / 5`. -/
lemma margin : (139 : ℚ) / 5 < -1600 * (A200 + U) := by
  unfold A200 U; norm_num

/-- The normalisation constant proved here (`Apery.Growth`): `limsup K⁻² log m_K ≤ A_eff`.
It is weaker than the paper's `A₂₀₀`, but still below `-U`. -/
def Aeff : ℚ := 136 / 100

/-- The margin used for irrationality: `A_eff + U < 0`. -/
lemma Aeff_margin : Aeff + U < 0 := by
  unfold Aeff U; norm_num

/-- `K = 40 n` as a real number. -/
noncomputable abbrev Kr (n : ℕ) : ℝ := 40 * (n : ℝ)

end Apery
