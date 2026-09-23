import Mathlib
import Apery.Growth.InnerSum
import Apery.Growth.OuterTable
import Apery.Growth.PieceIdx

/-!
# The integrals of the piece tables

`∑_i ∫_{t_i}^{t_{i+1}} (a_i x + b_i)/x³ dx` equals `(5.18)` for the inner table and
`127751/96000 + 9/640` for the outer table.
-/

open Finset intervalIntegral

namespace Apery

lemma integral_lin_div_cube (A B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (A * x + B) / x ^ 3 = A * (1 / a - 1 / b) + B / 2 * (1 / a ^ 2 - 1 / b ^ 2) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx; rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  have hb : 0 < b := by linarith
  rw [integral_eq_sub_of_hasDerivAt (f := fun x => -A / x - B / 2 / x ^ 2)]
  · field_simp; ring
  · intro x hx
    have hx0 := (hpos x hx).ne'
    have d1 := (hasDerivAt_const x (-A)).div (hasDerivAt_id x) hx0
    have d2 := (hasDerivAt_const x (B / 2)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
    have := d1.sub d2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact pow_ne_zero 3 (hpos x hx).ne'

lemma tIn_pos (i : ℕ) (hi : i ≤ 125) : 0 < tIn i := by
  have h0 : tIn 0 = 3 := by simp [tIn, tInL]
  have := grid_mono tIn_mono (Nat.zero_le i) hi
  linarith

lemma tOut_pos (i : ℕ) (hi : i ≤ 13) : 0 < tOut i := by
  have h0 : tOut 0 = 20 / 37 := by simp [tOut, tOutL]
  have := grid_mono tOut_mono (Nat.zero_le i) hi
  linarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem inner_integrals :
    ∑ i ∈ range 125, ∫ x in tIn i..tIn (i + 1), gIn i x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 := by
  rw [Finset.sum_congr rfl fun i hi => by
    have hi' := Finset.mem_range.mp hi
    exact integral_lin_div_cube _ _ (tIn_pos i hi'.le) (tIn_mono i hi').le]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tIn, tInL, aInL, bInL,
    List.getD_cons_succ, List.getD_cons_zero]
  norm_num

set_option maxHeartbeats 8000000 in
theorem outer_integrals :
    ∑ i ∈ range 13, ∫ x in tOut i..tOut (i + 1), gOut i x / x ^ 3 = 129101 / 96000 := by
  rw [Finset.sum_congr rfl fun i hi => by
    have hi' := Finset.mem_range.mp hi
    exact integral_lin_div_cube _ _ (tOut_pos i hi'.le) (tOut_mono i hi').le]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tOut, tOutL, aOutL, bOutL,
    List.getD_cons_succ, List.getD_cons_zero]
  norm_num

end Apery
