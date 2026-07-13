# X111–X130 faithfulness audit — the "next 20" wave (alphabetical std_* rows, chepoi…dvořák-mnich)

> Batch record for the 20 conjecture statements authored 2026-07-13, continuing the alphabetical
> walk through the studies-slice named-conjecture rows (`disposition=None`, `bucket=S6-promoted`)
> after X110 (chen-chvátal). Method: **author + independent second reader**, distinct agents, with
> machine-checked refutations where a row looked trivially true/false. Companion to
> `meta/X10-X110_faithfulness_audit.md`.

## Headline

- **20 rows processed** (X111–X130), one conjecture file each, all compile axiom-free
  (`Print Assumptions` = "Closed under the global context") under the `digraph` opam switch (Rocq 9.1.1).
- **16 done** (faithful) · **1 partial** (proxy) · **3 blocked** (out-of-scope foundation).
- **1 defect found and fixed** by the audit (X127) · **1 statement salvaged from blocked → done** (X114).
- v2 corpus moves **277 → 293 done, 0 → 1 partial, 1 → 4 blocked, 1351 → 1331 todo**.

This is a harder wave than X10–X110: the alphabetical tail hits coarse-structure, complexity,
width-parameter, hypergraph-Ramsey-tower, and probabilistic conjectures. Several needed either a
reused corpus foundation (D7 complexity layer, X27 tree-decompositions, X92 inversion, X98 induced
subdivision, X39 coarse balls) or an honest "blocked" classification.

## Per-row verdict

| # | conjecture (source) | area | state | verdict / note |
|---|---|---|---|---|
| X111 | Chepoi–Estellon–Vaxès r-ball τ≤c·ν | packing | done | FAITHFUL — one universal c (∃ before ∀), τ/ν on the same centre set, planarity guard |
| X112 | Chudnovsky–Penev–Scott–Trotignon χ-bounded closure | chromatic | done | FAITHFUL — inductive closure; both substitution & gluing constructors machine-checked satisfiable |
| X113 | Chudnovsky–Seymour coarse Erdős–Pósa | misc | done | FAITHFUL — ∃f,g before ∀; f=g=0 trivial witness refuted |
| X114 | Chudnovsky–Seymour–Trotignon subcubic H-ISC NP-complete | misc | done | PROXY (accepted, corpus-standard) — see below |
| X115 | Chvátal–Tuza max odd induced cycles | extremal | **partial** | PROXY — Θ(3ⁿ/³) form; literal "=3ⁿ/³" machine-refuted (K₆) — see below |
| X116 | Coarse Menger | misc | done | FAITHFUL — ℓ=f(k,d); confirmed DISTINCT from X39 (∀k ∃c ∀d, radius c·d) |
| X117 | Conlon–Fox–Rödl hedgehog Ramsey r(H_t;2)=t^{2+o(1)} | hypergraph | done | FAITHFUL — hedgehog structure machine-verified; two-sided rational-ε |
| X118 | Conlon–Fox–Sudakov dense pair | extremal | done | FAITHFUL — ε,σ before ∀G; fractional-power cross-multiplication correct |
| X119 | Conlon–Fox–Sudakov 3-uniform Ramsey tower | hypergraph | done | FAITHFUL — no-isolated-vertices guard machine-confirmed load-bearing (#V≤3m) |
| X120 | Conlon–Fox–Sudakov sparse pair | extremal | done | FAITHFUL — double fractional exponent correct; A,B forced nonempty |
| X121 | Dallard–Milanič–Štorgel (tw,ω)↔tree-α | minor | done | FAITHFUL — iff over all classes; tree-α via X27, matches vetted X102 idiom |
| X122 | Dijoin inversion-number additivity | digraph | done | FAITHFUL — dijoin & inv_eq (reusing X92) machine-verified; uniquely pins inv |
| X123 | Directed Gyárfás–Sumner {tournament, forest} | digraph | done | FAITHFUL — confirmed DISTINCT from X71 (pair, not forest-only) |
| X124 | Dreier–Toruńczyk merge-width poly-χ-bounded | chromatic | **blocked** | no merge-width foundation (placeholder antecedent) |
| X125 | Drier–Linial random-lift Hajós number | extremal | **blocked** | no random-lift / probability foundation |
| X126 | Dujmović Thue-choice ≤ pathwidth | chromatic | done | FAITHFUL — ∃f before ∀G; list-nonrepetitive + path-index decomposition |
| X127 | Dujmović–Joret–Morin–Norin–Wood 2-tree-width | minor | done | **DEFECT → FIXED** — faithful-to-refuted (Burling) — see below |
| X128 | Dvořák cheap balanced separators | misc | **blocked** | no bounded-expansion / real-cost separator foundation |
| X129 | Dvořák–Kráľ–Nejedlý–Škrekovski χ(G²)≤Δ+2 | chromatic | done | FAITHFUL — G²=graph_power G 2; girth≥5 via girth_geq (not has_girth) |
| X130 | Dvořák–Mnich planar-girth-5 χ_f<3 | chromatic | done | FAITHFUL — rational p/q<3 (χ_f rational); p=0 degenerate witness machine-refuted |

## The one defect — X127 (caught + fixed by the audit)

The author's first cut encoded **FJMTW's Conjecture 3** (a *spaghetti* tree-decomposition orthogonal
to a *path*-decomposition). The independent reader pulled the source (arXiv:1703.07871) and found
that is the WRONG statement for the row: the DJMNW "2-tree-width" is precisely the **median
tree-width** (min over **two arbitrary tree-decompositions** of the max pairwise bag-intersection),
and the DJMNW question *bounded 2-tree-width ⇒ bounded χ* is **refuted in that very paper** — the
Burling graphs have 2-tree-width ≤ 2 (Thm 2: a tree-decomposition and a path-decomposition with all
bag-intersections ≤ 2) yet unbounded χ (Thm 1). Conjecture 3 is a strictly weaker, still-open
statement, differently attributed. **Fix:** rewrote `x127_two_tree_width_le` to the true
median-width form (two arbitrary tree-decompositions, pairwise |B₁∩B₂| ≤ k). The statement is now
**faithful-to-refuted** (kept `done` with the note, exactly like the X10–X110 rows X14/X92/X73):
the formalization is faithful; the conjecture is resolved-negatively.

## The salvage — X114 (blocked → done)

Initially slated `blocked` (an NP-completeness *existence* question, like the blocked X90). But
graph-theory-misc already has a genuine **cost-coupled computation model** (`foundations/complexity.v`:
`prog`/`pcost`/`poly_cost_on`/`decides_on`) and D7's `problem`/`in_NP`/`NP_hard`/`poly_reduces` layer.
X114 reuses that layer plus X98's induced-subdivision model (byte-identical), so it is **authorable**:
`∃ subcubic H, in_NP(H-ISC) ∧ NP_hard(H-ISC)`. Classified **PROXY-done**: the graph content is fully
faithful and a trivial H is excluded (fails NP_hard), but D7's `NP_hard` is a *relational* proxy with
no machine model — classically it collapses (NP_hard(B) ≡ "B has a yes and a no instance"), though
this is **not** axiom-free refutable in Rocq's constructive logic (defining the reduction from the
`Prop` needs LEM/choice). This is the corpus-standard complexity reading; the same D7 layer backs the
`done` row `complexity_of_the_h_factor_problem`, so `done` is the consistent classification.

## The one partial — X115 (Θ-proxy)

Source: "the maximum number of odd induced cycles on n vertices *is* 3ⁿ/³." The literal exact reading
is **ill-posed** (3ⁿ/³ is irrational for n∉3ℤ, so an integer count can't equal it) and **machine-refuted**
at K₆ (count ≥ C(6,3)=20, 20³ = 8000 > 729 = 3⁶); the sharp asymptotic is also false (Morrison–Scott,
arXiv:1603.02960, resolved it as Θ with an n-mod-6-dependent constant). The author encoded the
**Θ(3ⁿ/³)** two-sided constant-factor form (cubed to stay integral, ∃Cu,Cl,N before ∀n). That is a
rigorous, non-vacuous, correctly-quantified statement, but a **documented weakening** of the source's
"= 3ⁿ/³" — so `partial` (proxy), under the disclosed reading "is 3ⁿ/³" = "of order Θ(3ⁿ/³)". This is
the corpus's category for approximation-proxies (cf. the rational-threshold and crossing-number rows).

## The three blocked (foundation deliberately out of scope)

Each ships a compiling `_statement` with the missing notion quantified abstractly / as an explicit
placeholder, a loud in-source `BLOCKED` comment, and `state: blocked` in `v2_statement_waves.json`
(no source-verification tuple claimed) — the same treatment as X90:

- **X124 (merge-width)** — poly-χ-boundedness (consequent) is faithful, but merge-width (Dreier–Toruńczyk
  2024, a tree of merge operations over a labelled-graph algebra) has no corpus foundation; the
  antecedent is a placeholder. Needs a merge-width layer.
- **X125 (random lifts)** — random ℓ-lifts of Kₙ, the Hajós number, and the "almost all"
  asymptotic-probability quantifier are quantified abstractly with no defining axioms. Needs a
  random-lift + probability foundation.
- **X128 (bounded expansion)** — bounded expansion (shallow-minor densities), real-valued cost
  assignments, cheap balanced separators, and outlier counts are quantified abstractly. Needs a
  bounded-expansion sparsity + real-cost separator foundation.

## Side finding (prior batch X10–X110) — X71 was false-encoded → INVESTIGATED & FIXED (2026-07-13)

While auditing X123, the digraph reader flagged **X71** (the *forest-only* directed Gyárfás–Sumner).
Investigation confirmed a **DEFECT (mis-encoding)**, now fixed:

- **The bug:** X71's source (1704.07219, 2212.02272) says "for every oriented forest F, Forb_ind(F) is
  χ⃗-**bounded**" — the dichromatic number is bounded by a **function** of the directed clique number
  ω⃗ (= order of the largest sub-tournament = ω of the underlying graph). X71 instead used
  `dichromatic_bounded` = a uniform **constant** bound (that is χ⃗-*finite*, X123's notion, not this
  row's). The constant form is **false**: Forb_ind(F) contains every tournament (a tournament has no
  induced copy of any oriented forest on ≥3 vertices — a forest has a non-adjacent pair, a tournament
  is semicomplete), and tournaments have unbounded dichromatic number, so no uniform B exists.
- **The fix:** rewrote the statement to the corpus directed-χ⃗-boundedness idiom (identical to the
  accepted **X54**): `∀ oriented forest F, ∃ f, ∀ oriented F-free D, dicolorableb D (f (ω([set:
  underlying D])))`. ω(underlying) is large on tournaments, so they no longer violate it; and forbidding
  a transitive tournament (X123) bounds ω⃗, turning this χ⃗-bounded statement into X123's χ⃗-finite one —
  so X71 (function bound) is the master form and implies X123. Compiles axiom-free; genuinely open;
  `check_milestone X71 digraph-theory` = ACCEPTED 10/10; X123 (which only references X71 in a comment)
  unaffected. Leg stays `done` (now faithful); wave note/provenance updated in `v2_statement_waves.json`.
- **Lesson:** the original single-reader readback accepted "bounded dichromatic number via the
  dichromatic_bounded wrapper" without checking χ⃗-**bounded** (function) vs χ⃗-**finite** (constant).
  The distinction is load-bearing across the directed-χ-boundedness rows (X54/X71/X123); the
  cross-audit against X123 is what surfaced it.

## Method / reproducibility

- **Authoring:** 8 area-grouped author subagents drafted the 16 feasible rows against a shared spec
  (`scratchpad/AUTHOR_SPEC.md`); the 3 blocked + X114 authored directly. Each file compiles
  standalone with its repo's `_CoqProject` flags via `opam exec --switch digraph -- coqc`.
- **Faithfulness:** 6 independent second-reader subagents (distinct from authors) audited all 16
  feasible rows against `scratchpad/AUDIT_SPEC.md`, machine-refuting suspects (K₆ for X115, p=0 for
  X130, constructor-satisfiability for X112, dijoin/inv uniqueness for X122, guard load-bearingness
  for X119). The X127 defect was caught here and fixed, then the fix re-compiled axiom-free.
- **Gates:** `make audit` (toolchain-free drift/invariants) green; `check_milestone Xnnn <repo>` =
  **20/20 ACCEPTED** (compiles + axiom-free + Print-Assumptions-clean + legs justified). Tracking:
  20 waves in `v2_statement_waves.json` → `build_v2_manifest.py` (extended to support `state: partial`)
  → `v2_corpus_manifest.json` + `v2_legs_state.json` → `CORPUS_STATUS.md`.
