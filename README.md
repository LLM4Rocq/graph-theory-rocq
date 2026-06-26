# graph-theory-rocq

A monorepo of Rocq/MathComp **graph-theory** libraries — the math-comp model (one repo,
many independently-installable opam packages). Each `<area>-theory/` subdir states the open
conjectures of one area of graph theory (and gains their proofs over time).

Built on [`coq-graph-theory`](https://github.com/rocq-community/graph-theory) (undirected) and
MathComp. The roadmap + the validated 227-problem manifest live in **`meta/`**.

## Packages
| package | namespace | core | deferred |
|---|---|---:|---:|
| `chromatic-theory/` | `Chromatic` | 32 | 0 |
| `digraph-theory/` | `Digraph` | 32 | 0 |
| `packing-theory/` | `Packing` | 15 | 0 |
| `cycle-theory/` | `Cycle` | 14 | 15 |
| `graph-theory-misc/` | `GTMisc` | 12 | 5 |
| `homomorphism-theory/` | `Hom` | 10 | 0 |
| `hamiltonicity-theory/` | `Hamilton` | 9 | 0 |
| `minor-theory/` | `Minor` | 6 | 0 |
| `reconstruction-theory/` | `Reconstruction` | 4 | 0 |
| `hypergraph-theory/` | `Hypergraph` | 4 | 0 |
| `topological-graph-theory/` | `Topological` | 4 | 14 |
| `extremal-graph-theory/` | `Extremal` | 0 | 32 |
| `infinite-graph-theory/` | `Infinite` | 0 | 14 |
| `spectral-graph-theory/` | `Spectral` | 0 | 5 |

Σ = 142 core + 85 deferred = 227.

## Layout
- `base/` — `coq-graph-theory-base`: the single owner of cross-area primitives (interop façade,
  homomorphism, products, list-χ, line/total-graph, Δ).
- `<area>-theory/` — the area packages (each: foundations/core/invariants/constructions/conjectures/applications).
- `atlas/` — cross-area `_implies_` edges + the federated conjecture dependency graph.
- `blueprint/` — shared dev tooling (statement-closure gate, correspondence auditor, axiom audit, site generator).
- `meta/` — the roadmap (`OPG_FULL_FORMALIZATION_PLAN.md`), the manifest, and its builder/loader.

`digraph-theory/` was absorbed from the standalone repo via a subtree merge (history preserved).
See `meta/OPG_FULL_FORMALIZATION_PLAN.md` §A / §A.1.
