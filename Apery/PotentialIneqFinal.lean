import Apery.Table2.All

/-!
# The potential inequality (6.2), Lemma 6.1

`2 Uρ(t) - V(t) ≤ M₀` for all `t > 0`, from the certified verification over the Table 2 partition
of `(0, 2]` and the tail bound for `t ≥ 2`.
-/

namespace Apery

/-- **Lemma 6.1**, the potential inequality (6.2). -/
theorem potential_ineq {t : ℝ} (ht : 0 < t) : 2 * Uρ t - Vfield t ≤ M0 := by
  rcases le_or_gt t 2 with h | h
  · exact potential_ineq_le_two t ht h
  · exact potential_ineq_tail h.le

end Apery
