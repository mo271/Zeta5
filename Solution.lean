import Apery.Main

namespace RiemannZetaValues

theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x := by
  exact Apery.irrational_five

end RiemannZetaValues
