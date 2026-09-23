import Mathlib
import PrimeNumberTheoremAnd.Consequences

/-!
# The prime number theorem, imported from `PrimeNumberTheoremAnd`

The normalisation step (Proposition 5.2 of the paper) needs the prime number theorem in the
form `θ(x) ~ x` for Chebyshev's function `θ`. Mathlib does not contain it; the
`PrimeNumberTheoremAnd` project (added as a path dependency) does.
-/

open Filter Asymptotics

namespace Apery

/-- Chebyshev's function `θ(x) = ∑_{p ≤ x} log p` is asymptotic to `x`. -/
theorem theta_asymptotic : Chebyshev.theta ~[atTop] id := chebyshev_asymptotic

end Apery
