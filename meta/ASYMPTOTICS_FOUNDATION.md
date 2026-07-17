# Asymptotics Foundation Notes

Status: phase 1 started on 2026-07-16.

## Promoted Layer

`base/theories/asymptotics.v` is the package-neutral, nat-valued asymptotic layer re-exported by `GTBase.base`.

It now owns:

- `eventually`, `eventually_le`, `eventually_ge`
- `big_O_nat`, `big_Omega_nat`, `big_Theta_nat`
- `big_O_with_slack_nat`
- `little_o_nat`
- `polynomial_bound_nat`
- `subpolynomial_nat`
- `near_linear_lower_nat`
- `sqrt_ceil`

The rational-epsilon predicates are encoded by cross multiplication over `nat`. This is faithful for statement rows whose informal asymptotics are only used as finite eventual inequalities, for example:

- "for all sufficiently large n"
- `f = O(g)`, `f = Theta(g)`, or `f = o(g)` for nat-valued envelopes
- polynomial upper bounds with an additive finite-size slack
- `n^(1-o(1))` lower bounds via `near_linear_lower_nat`
- ceiling-square-root finite upper bounds

## Grounding

The module includes small sanity lemmas rather than conjectural facts:

- `eventually_true`
- `big_O_nat_refl`
- `big_Theta_nat_refl`
- `big_Theta_nat_2n_n`
- `little_o_zero_nat`
- `polynomial_bound_nat_const`
- `sqrt_ceil_spec`

Representative `Print Assumptions` checks for `sqrt_ceil_spec`, `big_Theta_nat_2n_n`, and `little_o_zero_nat` are closed under the global context.

## Faithfulness Boundary

This layer deliberately does not yet cover:

- real-valued logarithms, square roots, or real Landau notation
- probability/with-high-probability statements
- analytic graph-limit notions
- structural graph class foundations such as bounded expansion, merge-width, or random lifts

Rows in those categories should remain blocked or use an area-local faithful layer until a matching foundation is promoted.

## Retargeted Rows

- `X175` now uses `eventually` for the rational-epsilon
  `3^(2t/3+o(t)) n` upper envelope, together with a concrete local
  `K_t`-subdivision predicate.
- `X209` now uses `big_Theta_nat` for the finite
  `excess(m)^2 = Theta(m)` encoding of a `Theta(sqrt m)` hypergraph-cut
  excess conjecture, together with concrete local cut/excess definitions.
- `X206` now uses rational cross-multiplication for the real parameter
  `c > 1` and integer exponentiation for the condition
  `omega(G) <= Delta(G)^(1/f(c))`, tied to base's `is_choice_number`.
