Numerical checks of the paper "ζ(5) is irrational" (requires `pip install python-flint sympy`).

* `hankel.py n1 n2 ...` — computes `Δ_K(X) ∈ ℚ[X]` exactly for `K = 40 n` (via
  `Δ = det(B) · charpoly(−B⁻¹A)` where `G_K(X) = A + X B`), checks the leading coefficient
  formula (2.9), and evaluates `Δ_K`, `F_K` and the primitive polynomial `P_K` at `ζ(5)`
  with rigorous ball arithmetic.
* `valuations.py n1 n2 ...` — factors the content of `Δ_K` and checks the bound (3.12) at every
  prime, integrality for `p > K`, and the outer-range bound `γ_p^out` of (4.14) / Prop. 4.3.
* `appendixB.py` — recomputes, with exact rationals, the inner integral (5.18) and Table 3 from
  the definitions (5.4)–(5.6), the outer integral (5.10) and Table 4 from (5.8)–(5.9), and
  checks the consistency of `A*` (5.19); also samples the bound (5.14).
* `lemma61.py` — recomputes the potential inequality (6.2) of Lemma 6.1 over the 684 intervals
  of Table 2 (`max B(l,r) = -6.6450027 < -6.645002`), checks that they partition `[0, 2]`, the
  location of the minimum of `V`, and (6.8) at `t = 2`.

## `growth/`

Generators for the growth bound (`Apery/Growth/*`), run from within `scripts/growth/`:

* `gen_pieces.py`: computes the 125 exact linear pieces of `Ê_in` on `[3, 20]` (writes
  `pieces.pkl`) and checks that they integrate to (5.18).
* `outer_gen.py`: the 13 pieces of `Ê_out` on `[20/37, 3]` (writes `outer_pieces.pkl`); integral
  `129101/96000`.
* `gen_lean_inner.py`, `gen_inner_sum.py`, `gen_lean_outer.py`: emit `InnerTable.lean`,
  `InnerSum.lean`, `OuterTable.lean` from the pickled pieces.
* `growth.py`, `table.py`: reference implementations (the paper's `R(x)` and the Lean-style
  `Ê_in`); `budget2.py`: numerical budget of the total constant.
