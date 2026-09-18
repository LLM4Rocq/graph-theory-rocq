# graph-theory-rocq

![corpus-status](https://github.com/LLM4Rocq/graph-theory-rocq/actions/workflows/corpus-status.yml/badge.svg)
**OpenProblemGarden corpus: statement-complete** — 227/227 attempted · **208 done** (axiom-free
`Definition <name>_statement : Prop`, `Print Assumptions` clean) · **12 partial** · **7 blocked**.
Release: **`opg-v1.0.1-227-attempted`** (release-time counts 212/8/7; 4 crossing-number rows were
since downgraded to partial — `meta/CORPUS_STATUS.md` is the canonical living report). v1
completion report: [`meta/OPG_FULL_FORMALIZATION_PLAN.md`](meta/OPG_FULL_FORMALIZATION_PLAN.md).

**v2 corpus (growing)** — every conjecture source of the upstream `graph-conjectures` repo:
**1,745 rows tracked** (762 arXiv + 277 erdősproblems + 138 attack-engine derived + 568
studies-slice) · ~1,075 statement-owing after triage, the rest parked/alias/edge-anchor with
documented dispositions · **312 statements done · 1 partial · 65 blocked** (waves X1–X210: directed reconciliation +
directed/χ-boundedness/extremal/structural/topological/cycle/minor/misc/packing/quasi-kernel/reconstruction/deck/nonrepetitive/normal/treewidth/total-list/linear-arboricity/coarse-Menger/coarse-Erdős–Pósa/tree-decomposition/hedgehog-and-3-uniform-Ramsey/Erdős–Hajnal-pairs/dijoin-inversion/directed-Gyárfás–Sumner/fractional-and-distance-colouring/induced-subdivision-complexity authored statements — every one
axiom-free with a faithfulness audit recorded in the manifest; blocked rows need a foundation deliberately out of scope, e.g. merge-width, random-lift probability, bounded-expansion sparsity, fixed-surface clustered colouring, graphon forcing, asymptotic dimension, computation-model, random-graph, DP-colouring, Kempe-class, polyhedral extension-complexity, metric-line/bridge-generation, poset-dimension, flow, thin-overlay, Ramsey-nice, cops-and-robbers, hypergraph-cut, or conflict-colouring layers). Plan:
[`meta/V2_FULL_CORPUS_PLAN.md`](meta/V2_FULL_CORPUS_PLAN.md); live counts in
[`meta/CORPUS_STATUS.md`](meta/CORPUS_STATUS.md).

A monorepo of Rocq/MathComp **graph-theory** libraries — the math-comp model (one repo,
many independently-installable opam packages). Each `<area>-theory/` subdir states the open
conjectures of one area of graph theory (and gains their proofs over time).

Built on [`coq-graph-theory`](https://github.com/rocq-community/graph-theory) (undirected) and
MathComp. The roadmap + the validated 227-problem manifest live in **`meta/`**. Verify the
statement-complete claim with `make audit` (toolchain-free) or the full `make gate` (Coq builds).

## Building

Everything here is Rocq 9.1 + MathComp 2.5 + [`coq-graph-theory`](https://github.com/rocq-community/graph-theory) 0.9.7.
A full clean build of the whole corpus takes about six minutes.

### 1. One-time toolchain setup

```sh
opam switch create digraph ocaml-base-compiler.5.2.1
eval $(opam env --switch=digraph)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-graph-theory.0.9.7 rocq-mathcomp-classical.1.16.0
```

Those two packages pull in everything else: `rocq-core` 9.1.1, `rocq-stdlib` 9.0.0,
MathComp 2.5.0 (`ssreflect`/`algebra`/`fingroup`/`finmap`) and Hierarchy-Builder 1.10.2.
Budget 15-30 minutes — opam builds it all from source.

Name the switch `digraph` if you can: the gates in `meta/` look for `~/.opam/digraph` by
default. Any other name works too, as long as you either put it on `PATH` (`eval $(opam env)`)
or point the gates at it explicitly with `ROCQ_OPAM_SWITCH=<switch-name>`.

### 2. Build

```sh
make all -j4              # base + classical-lemmas + the 13 area packages
make digraph-theory -j4   # the absorbed Digraph package
```

`make all` is 356 files, ~3.5 min; `digraph-theory` is 118 files, ~2.5 min (4 cores, warm
switch — roughly double that on CI-class hardware). `digraph-theory` is kept out of `all`
because its proofs are the heaviest in the repo; its P9 milestone is still covered by
`make gate`.

Build one package on its own with `make chromatic-theory`, and start over with `make clean`.
Each package target is just `rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq`
run inside that directory, so you can drop down to `Makefile.coq` for a single file.

### 3. Check the corpus claims

```sh
make audit    # no Rocq needed — python3 only, a few seconds
```

`make audit` verifies that the committed manifest, leg-state overlay, dependency graph and
`meta/CORPUS_STATUS.md` are mutually consistent. This is what CI runs.

The full acceptance gate additionally builds every landed milestone and checks it is
axiom-free with `Print Assumptions` clean:

```sh
git clone https://github.com/graph-theory-AI/graph-conjectures ../../graph-conjectures
make gate
```

`make gate` regenerates the manifest from the upstream conjecture source, so it needs that
checkout. It is looked for at `../../graph-conjectures` relative to this repo (i.e. a sibling
of this repo's parent); override with `GRAPH_CONJECTURES=/path/to/graph-conjectures`. Pin it to
`f6901fb371155678980a84306f6208fa0f166a6b` to reproduce the committed manifest exactly.

### Note on `digraph-theory/theories/applications/ck_path`

Those DRUP certificate files are **generated, not committed** — `scripts/generate_ckpath_certificates.py`
writes them and `.gitignore` excludes them. A fresh clone builds the 118 tracked `Digraph` files in
~2.5 min; if you have generated the certificates locally, the same command builds ~1,400 files
instead and takes considerably longer.

## Checked formal resolutions

Six source records have checked formal resolutions: five new formalizations and a bridge to the existing Question 5.9 counterexample family. The latest additions disprove directed Kneser existence at `(5,3)` and the printed Alon–Tarsi Question 6.1. All six have closed assumptions.

See the [proof overview](meta/formalizations/README.md), [latest development journal](meta/formalizations/ROUND2_JOURNAL.md), and [resolution registry](meta/FORMAL_RESOLUTIONS.md). Run `ROCQ_OPAM_SWITCH=rocq-tools make resolutions` to build and check them with the compatible development switch.

## Checked repairs of proof gaps

The frozen-colouring switching bound and a six-cycle viability certificate now
have Rocq proofs. These are scoped results toward two source conjectures; the
full dynamics and planar-construction conclusions remain unformalized. See the
[repair audit](meta/GAP_REPAIRS.md) and [development journal](meta/GAP_REPAIRS_JOURNAL.md).
Run `ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs` to compile the artifacts and
check their exact theorem types and closed assumptions.

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
- `meta/` — the v1 completion report + roadmap (`OPG_FULL_FORMALIZATION_PLAN.md`), the validated 227-row
  manifest + leg-state overlay, the federated dependency graph (`dependency_graph.json`), the status report
  (`CORPUS_STATUS.md`), and the gates (`check_milestone.py`, `report_corpus_status.py`, `build_edge_graph.py`).
- `atlas/`, `blueprint/` — *scaffolds* reserved for later extraction of the cross-area edge atlas and the
  shared dev tooling; both currently live in `meta/` (see the stubs' `Status: scaffold`).

`digraph-theory/` was absorbed from the standalone repo via a subtree merge (history preserved).
See `meta/OPG_FULL_FORMALIZATION_PLAN.md` §A / §A.1.
