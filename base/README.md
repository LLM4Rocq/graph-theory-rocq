# graph-theory-base (`coq-graph-theory-base`, namespace `GTBase`)

The single owner of **cross-area primitives** for the graph-theory-rocq federation (plan §A
ownership table). Every area package depends ONLY on this (never on a sibling).

**Status: G3-core LANDED (2026-06-26).** `theories/base.v`:
- **re-exports** the core coq-graph-theory undirected vocabulary in one place — `sgraph`, `--`,
  `N(x)`, `χ`/`chi_mem`, `ω`/`omega_mem`, `α`, `clique`/`cliques`, `connected`, `'K_n`/`complete`,
  `≃`/`diso`, `ucycle`/`ucycleb` (plus mathcomp `all_boot`);
- **owns** the cross-area primitives:
  - from U1: `Delta` (Δ), `common_nbr`, `regular`, `girth_geq`, `ceil_div`;
  - U3 surface (+ `cartesian_product` promoted from U2): graph homomorphism `is_hom` /
    `homs_to`, graph `is_core`, `cartesian_product` (□), `tensor_product` (×, the Hedetniemi product);
  - power family (promoted from U1 ∩ U3): `graph_power` (Gᵐ), `subdivision` (G^{1/n}), `frac_power` (G^{m/n});
  - list-colouring (promoted from U4): `list_colourable` / `list_colourable_on` (over an arbitrary
    `finType` palette), `choosable` (k-choosability), `is_choice_number` (relational choice number);
  - edge/total colouring (promoted from U4, the `mgraph` layer): the `mgraph` notation (`graph unit unit`),
    `line_graph` / `total_graph` (undirected sgraphs), `chromatic_index` (χ'), `total_chromatic_number`
    (χ''), `edge_colourable` / `total_colourable`. **`mgraph` is `Import`ed, not `Export`ed** — a
    pure-sgraph milestone stays clean; an mgraph-aware milestone does `From GraphTheory Require Import
    mgraph.` **before** the base import (coq-graph-theory's `mgraph` has a clashing *directed* `line_graph`).
    `mDelta` (multigraph max degree, parallel edges counted) is here too (promoted from U4 ∩ U5).
  - connectivity & structure (promoted across U2/U3/U6/U9): `k_connected` (Whitney form),
    `triangle_free` (vertex-triple form), `uwalk` (undirected multigraph walk — fixes the
    source→target bias of coq-graph-theory's `walk`; cycle-theory/U6 connectivity reuses it).

Import with `From GTBase Require Import base.` (area packages add `-Q ../base/theories GTBase`
to their `_CoqProject`). Compiles axiom-free on switch `digraph` (Rocq 9.1.1 + coq-graph-theory);
`chromatic-theory/U1` consumes it.

**Not here yet:** graph homomorphism / products / list-χ / line-graph (added as the milestones
that need them land), and the **planarity façade** (gated on the `coq-fourcolor` spike, G2).
