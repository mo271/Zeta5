# Zeta5

Lean 4 / Mathlib formalization of

```lean
theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x
```

The proof follows A. Fauzan’s preprint, *ζ(5) is irrational* (17 September
2026). The project is licensed under Apache 2.0.

## Project map

- `Challenge.lean` contains the benchmark statement, copied from the Formal
  Conjectures declaration
  [`RiemannZetaValues.irrational_five`](https://github.com/google-deepmind/formal-conjectures/blob/2db01438fda960163f58ff2c2385b52e53f56dd2/FormalConjectures/Wikipedia/RiemannZetaValues.lean).
- `Solution.lean` proves the same statement using `Apery.irrational_five`.
- `Apery/` contains the proof development.
- `config.json` and `.github/workflows/comparator.yml` configure Comparator
  verification.

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4), pinned to
  `f385f9fd18abed332ebcd3df239cb357e264aceb` for Lean `v4.34.0-rc1`.
- [PrimeNumberTheoremAnd](https://github.com/mo271/PrimeNumberTheoremAnd),
  imported by `Apery/PNT.lean` for the prime number theorem.
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
  supplies the challenge statement; it is cited above rather than imported
  as a project dependency.

The checked proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
