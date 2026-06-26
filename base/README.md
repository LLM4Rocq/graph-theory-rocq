# graph-theory-base (`coq-graph-theory-base`, namespace `GTBase`)

The single owner of **cross-area primitives** for the graph-theory-rocq federation (plan §A
ownership table). Every area package depends ONLY on this (never on a sibling).

**Status: G3-core LANDED (2026-06-26).** `theories/base.v`:
- **re-exports** the core coq-graph-theory undirected vocabulary in one place — `sgraph`, `--`,
  `N(x)`, `χ`/`chi_mem`, `ω`/`omega_mem`, `α`, `clique`/`cliques`, `connected`, `'K_n`/`complete`,
  `≃`/`diso`, `ucycle`/`ucycleb` (plus mathcomp `all_boot`);
- **owns** the cross-area primitives discovered + validated by the U1 milestone:
  `Delta` (Δ), `common_nbr`, `regular`, `girth_geq`, `ceil_div`.

Import with `From GTBase Require Import base.` (area packages add `-Q ../base/theories GTBase`
to their `_CoqProject`). Compiles axiom-free on switch `digraph` (Rocq 9.1.1 + coq-graph-theory);
`chromatic-theory/U1` consumes it.

**Not here yet:** graph homomorphism / products / list-χ / line-graph (added as the milestones
that need them land), and the **planarity façade** (gated on the `coq-fourcolor` spike, G2).
