# `theories/conjectures/` — digraph conjectures, stated (not proved) + their dependency graph

This package formalizes the **statements** of the directed-graph conjectures tracked in
`~/Recherche/graph-conjectures` (the OpenProblemGarden mirror + arXiv DB), together with a
**dependency graph** whose edges are machine-checked implications between them. See
`docs/CONJECTURES_FORMALIZATION_PLAN.md` for the full plan, corpus, and phase map.

## Conventions

- **Nodes.** Each conjecture is a `Definition <name>_statement : Prop := …`. This
  type-checks the statement and introduces **no axiom** (the main library stays
  axiom-free). A named open target `Conjecture <name> : <name>_statement.` — which *is* an
  axiom — may be placed in a separate `_targets.v`, never in the statement files.
- **Edges.** An implication "A ⟹ B" is a `Qed`-closed relative theorem
  `Theorem <A>_implies_<B> : <A>_statement -> <B>_statement.` — provable *without*
  resolving either conjecture. Equivalences use `_equiv_`; negations of refuted
  conjectures are stated as `~ <name>_statement`.
- **Factoring.** Statements must share granularity so edges type-check: a special case is
  the general statement *instantiated*; one shared definition per recurring notion
  (`ω̄`/`omegabar`, `χ⃗`, `unvd`, `Forb_ind`); weakenings phrased so the strengthening
  visibly implies them.
- **External lemmas (`external.v`).** When an edge relies on a cited published theorem not
  formalized here, declare it as a `Definition Z_statement : Prop` in `external.v` and
  carry it as an explicit hypothesis (`Z_statement -> A_statement -> B_statement`). Never
  `Admitted`/axiomatize — edges stay `Qed`-closed and their external dependencies greppable.

## Layout (grows by phase)

- `external.v` — cited results as hypothesis-`Prop`s.
- `clique_cluster.v` — AACL ω̄-cluster (Conj 5.10, Q5.9, 5.8, dom⇒ω̄-cluster) + edges. [P1]
- `long_dipath.v` — Cheng–Keevash / Thomassé long-directed-path conjecture + edges. [P1]
- *(later: `implications/` for cross-paper edges; `chordal_chivec.v`, `heroes.v`, `sad.v`,
  `classic_core.v` (Seymour 2nd-nbhd, Caccetta–Häggkvist), … per the plan.)*

## Extraction

The dependency graph is recovered by scanning `_implies_`/`_equiv_` theorems (naming
convention above) → `docs/dependency_graph.json` → rendered via `site/`.
