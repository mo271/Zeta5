import Mathlib
import Apery.Criterion
import Apery.MainEstimate

/-!
# Irrationality of ζ(5)

`Apery.irrational_five` is the target statement. It follows from `Apery.main_estimate`
(Theorem 2.1 of the paper, with a smaller decay rate) and the criterion
`Apery.irrational_of_eventually_exists_int_poly`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Polynomial Filter Topology

namespace Apery

/-- Theorem 1.1 of the paper, from Theorem 2.1. -/
theorem irrational_zeta5 : Irrational zeta5 := by
  obtain ⟨c, hc, h⟩ := main_estimate
  exact irrational_of_eventually_exists_int_poly zeta5 (fun n => 37 * n)
    (fun n => Real.exp (-c * (n : ℝ) ^ 2))
    (tendsto_pow_mul_exp_neg_sq_of_pos hc)
    (h.mono fun _ ⟨Q, _, hdeg, hpos, hlt⟩ => ⟨Q, hdeg.le, hpos, hlt.le⟩)

theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  ⟨zeta5, irrational_zeta5, riemannZeta_five⟩

end Apery
