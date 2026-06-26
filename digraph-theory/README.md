# digraph-theory

**Directed graphs and tournaments for the Rocq / MathComp ecosystem.**

A formal library for *directed* graph theory built on
[MathComp](https://github.com/math-comp/math-comp) and
[mathcomp-classical](https://github.com/math-comp/analysis), targeting
mathematicians (classical logic; no constructivity constraint). It is the
**directed companion to [coq-graph-theory](https://github.com/rocq-community/graph-theory)**:
the undirected clique / colouring / minor machinery is *reused* from there; this
library adds what is missing for digraphs and tournaments.

First concrete goal — **achieved**: a formalised infinite family of
`5`-`ω̄`-critical tournaments `ACₙ[ACₙ]`, proving
**Aboulker–Aubian–Charbit–Lopes Conjecture 5.10 at `k = 5`** and showing
**Question 5.9 fails at `k = 5`** (`applications/k5/main.v`, axiom-free). The
full design, module map, and milestone roadmap are in
**[`docs/DESIGN.md`](docs/DESIGN.md)**.

## Status

**Milestones M1–M3 — done (2026-06-11). The reusable directed/tournament
theory is complete (first public release point).**
M1: the HB hierarchy (`DiGraph` → `Tournament`), vertex orders as permutations
with the order-realization theorem, the backedge graph as a graph-theory
`sgraph`, and the tournament clique number `ω̄` (realized minimum, ω̄ = 1 ⟺
transitivity, monotonicity under embeddings / sub-tournaments / deletion,
iso-invariance); exit theorems `ω̄(C3) = 2`, `ω̄(TTₙ) = 1`, and C3 the *unique*
2-ω̄-critical tournament. M2: automorphism groups and vertex-transitivity, the
lexicographic substitution `S[H]` (tournament-closed), Cayley digraphs
(tournament iff `A ⊎ A⁻¹ = G∖{1}`; vertex-transitive via translations), and
circulants over `'Z_n` — the paper's `AC m` on `2m+1` vertices is a canonical,
vertex-transitive tournament. M3, the three marquee general theorems:
**substitution lower bound** `ω̄(S)+ω̄(H) ≤ ω̄(S[H])+1`, **vertex-transitive ⇒
uniform deletion** (criticality needs a single deletion), and **directed
domination** with `dom(T) ≤ ω̄(T)`. Everything axiom-free and cross-checked
against the exact Python oracle in [`scripts/`](scripts/). The target paper
lives in [`paper/`](paper/). Dev switch: opam switch `digraph` (Rocq 9.1.1 +
MathComp 2.5.0 + mathcomp-classical 1.16.0 + coq-graph-theory 0.9.7), linked
to this directory.

**M4 (the ACₙ base facts) — done (2026-06-11):** for every n = 2m+1 with
m ≥ 3, `ω̄(ACₙ) = 3` (bucket pigeonhole up; domination + the
interval-autocorrelation lemma down), `ω̄(ACₙ − v) = 2` for all v, and ACₙ is
**3-ω̄-critical** — paper Proposition "Facts about ACₙ", axiom-free,
oracle-checked on AC₇/AC₉.

**M5 (lower bounds for T = ACₙ[ACₙ]) — done (2026-06-11):**
`ω̄(T) ≥ 5` and `ω̄(T − (0,0)) ≥ 4`, both directly from the M3 substitution
theorem and the M4 values.

**M6 (upper bounds + assembly) — done (2026-06-11). The formalization of the
paper is complete.** Lemma H17 (`in_neighbourhood`), the 9-cell key order and
the cell Lemma (`cells`), the 20 infeasible cell-sets (`obstructions`), the
256-case coverage check (`coverage` — the one n-independent computational
step), giving `ω̄(T) ≤ 5` and `ω̄(T − (0,0)) ≤ 4` (`k5_upper`). `main.v`
assembles, for every odd `n = 2m+1 ≥ 7`: **`ω̄(ACₙ[ACₙ]) = 5`**,
**`ω̄(T − v) = 4` for every v** (by vertex-transitivity of the product, added
to `constructions/product.v`), **`T5_kcritical5`** (5-ω̄-critical, order
`n²`), **`conjecture_5_10_at_k5`** (the infinite family), and
**`question_5_9_fails_at_k5`** (every proper subtournament has `ω̄ ≤ 4`, so
no bound `ℓ(5)` exists). All exit theorems `Print Assumptions`-clean.

**K34 (M13–M17) — done (2026-06-12): the unified k = 3, 4, 5 theorem.**
`conjecture_5_10_at_345` (`applications/unified.v`): **for every
k ∈ {3, 4, 5} there are infinitely many k-ω̄-critical tournaments** — the
three families over the same circulant platform: ACₙ (k = 3, already M4),
**ACₙ[C₃] (k = 4, new: `applications/k4/`)** and ACₙ[ACₙ] (k = 5).
The k = 4 case (`omegabar_T4 = 4`, `omegabar_T4_del = 3` ∀v,
`T4_kcritical4`, order 3n) runs on the merged-class order kv for the
value bound (`k4_value`) and the five-band d_then_c order kd for the
deletion bound (`k4_del` — the (2,2)-core: 1+δ ∈ g and m+1+δ ∈ g are
incompatible for δ ∈ g). Question 5.9 now fails at *each* k ∈ {3,4,5},
all through the new general `kcritical_proper_sub`. D12 dividends:
`card_classes`/`card_classes_inj` (prelude), the shared ACₙ band kit
(`applications/acn_bands.v`, relocated from k5), `C3_vertex_transitive`.
All 13 new exits `Print Assumptions`-clean; plan in `docs/PLAN_K34.md`,
dossier in `docs/k34_dossier.md`, oracle `scripts/k4_oracle.py`
(114 tests).

**CK3 (M7–M12) — done (2026-06-11): the δ = 3 path theorem.**
`ck_conj1_delta3`: every nonempty oriented digraph with minimum out-degree
≥ 3 contains a directed simple path of length 6 — the δ = 3 case of
Cheng–Keevash Conjecture 1 (Thomassé's path conjecture), formalizing the
hand proof of the companion search project. On the way the library gained
the `Oriented` structure, directed simple paths and ℓ(D) (`core/dipath`),
strong connectivity with the sink-SCC reduction (`invariants/strong`),
and — uniform in δ — **Cheng–Keevash Lemma 7** with its corollaries
`ck_theorem4_oriented` (ℓ ≥ 2δ − ⌊(δ−1)/2⌋) and the δ = 2 case
(`applications/ck3/`). All axiom-free; plan in `docs/PLAN_CK3.md`,
self-contained proof dossier in `docs/ck3_dossier.md`.

## What's here / coming

| Layer | Module(s) | Milestone |
|---|---|---|
| Foundations | `foundations/prelude` ✅, `foundations/interop_graph_theory` ✅ | M0–M1 |
| Core | `core/digraph` ✅, `core/tournament` ✅, `core/order` ✅ | M1 |
| Invariants | `invariants/omegabar` ✅, `…/critical` ✅, `…/domination` ✅, `…/dichromatic` | M1–M3 |
| Constructions | `constructions/{product,cayley,circulant,automorphism}` ✅ | M2 |
| General theorems | `substitution` ✅, `transitive` ✅ | M3 |
| Application (k=5) | `applications/k5/{acn_arc_facts,acn_base,k5_lower,in_neighbourhood,cells,obstructions,coverage,k5_upper,main}` ✅ | M4–M6 |
| Application (CK3) | `applications/ck3/{lemma7,ck3_main}` ✅ + `core/{oriented,dipath}` ✅, `invariants/strong` ✅ | M7–M12 |
| Application (k=4) + unified | `applications/k4/{k4_lower,k4_value,k4_del,k4_main}` ✅, `applications/{acn_bands,unified}` ✅ | M13–M17 |

## For mathematicians: the statement-audit site and PDF

**You do not need Rocq to check what was proved.**
The interactive site

> **https://llm4rocq.github.io/digraph-theory/**

gives one page per headline result with the *verbatim* formal
statement, a plain-mathematics decoding, and links to **every**
definition the statement depends on (with faithfulness notes), plus a
clickable dependency graph — and no proofs (the kernel checked those;
every result is axiom-free). The same content with a notation primer
and the full declaration catalog is the companion PDF
[`digraph_formal.pdf`](https://llm4rocq.github.io/digraph-theory/digraph_formal.pdf)
(source in [`docs/formal/`](docs/formal/)). The definition lists are
*generated from the compiled library* and CI fails if a statement's
dependency closure ever escapes the documented dictionary
(`scripts/statement_closure.py`, see [`docs/PLAN_WEB.md`](docs/PLAN_WEB.md)).

For the **informal ⇄ formal correspondence** — every conjecture *and* proved
result paired with its informal source, a plain-English readback of the formal
statement, the verbatim Rocq, the proved implication edges, and the
**machine-checked grounding proofs that test each definition** (the non-vacuity
/ satisfiability witnesses and discriminating refutations, browsable on their
own and cross-linked from each statement) — see the interactive auditor at

> **https://llm4rocq.github.io/digraph-theory/correspondence/**

generated by [`scripts/build_correspondence.py`](scripts/build_correspondence.py)
from the hand-authored mapping in
[`docs/correspondence/curated.json`](docs/correspondence/) (CI gate:
`build_correspondence.py --check` requires an authored readback for every entry).

## Build

Requires Rocq/Coq ≥ 8.19, MathComp ≥ 2.5.0, mathcomp-classical ≥ 1.16.0,
Hierarchy Builder ≥ 1.5.0. (From M1, also `coq-graph-theory` ≥ 0.9.7.)

```sh
# in an opam switch with the dependencies above
make            # builds everything listed in _CoqProject
make clean
```

The build delegates to a `Makefile.coq` generated from `_CoqProject` via
`coq_makefile` / `rocq makefile` — the standard rocq-community pattern. `coqc`
finds the MathComp dependencies automatically (opam `user-contrib`).

## Installing dependencies (example)

```sh
opam switch create . --packages=rocq-prover.9.1.1     # or reuse an existing switch
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-mathcomp-ssreflect rocq-mathcomp-algebra \
             rocq-mathcomp-fingroup rocq-mathcomp-classical rocq-hierarchy-builder
# from M1:
opam install coq-graph-theory
```

## Conventions

- File names are lowercase (`tournament.v`, `omegabar.v`), matching MathComp and
  graph-theory; structure identifiers keep the usual MathComp casing.
- Lower layers never depend on higher ones; `coq-graph-theory` is imported in
  exactly one file (`foundations/interop_graph_theory.v`).
- See [`CONTRIBUTING.md`](CONTRIBUTING.md) and [`docs/DESIGN.md`](docs/DESIGN.md).

## License

Apache-2.0 — see [`LICENSE`](LICENSE).
