/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Irrationality of ζ(5)

This challenge statement is copied verbatim from the Formal Conjectures
repository, `FormalConjectures/Wikipedia/RiemannZetaValues.lean`, theorem
`RiemannZetaValues.irrational_five`, at commit
[`2db01438fda960163f58ff2c2385b52e53f56dd2`](https://github.com/google-deepmind/formal-conjectures/blob/2db01438fda960163f58ff2c2385b52e53f56dd2/FormalConjectures/Wikipedia/RiemannZetaValues.lean).
-/

namespace RiemannZetaValues

/--
$\zeta(5)$ is irrational.
-/
theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x := by
  sorry

end RiemannZetaValues
