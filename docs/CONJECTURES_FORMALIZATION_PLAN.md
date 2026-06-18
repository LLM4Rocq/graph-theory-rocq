# Formalizing the digraph conjectures — a STATEMENT-only plan

**Goal.** State (not prove) in Rocq/MathComp every directed-graph conjecture in the
`~/Recherche/graph-conjectures` corpus — **the whole website (OpenProblemGarden) + the
arXiv-mined database**, not just the actively-worked problem folders. Each conjecture
becomes a `Definition <name>_statement : Prop := …` that type-checks and introduces **no
axiom**, optionally with a companion `Conjecture <name> : <name>_statement.` as a named
open goal. Proofs are out of scope.

**Status:** v2 (2026-06-18). v1 scoped only the 11 actively-attacked `problems/` folders;
v2 expands to the full corpus after a classification survey of **148 records → ~98 unique
conjectures** (142 open). Source artifacts in this repo:
- `docs/digraph_conjecture_ledger.json` — the raw corpus: 37 OPG digraph problems + 111
  arXiv digraph records, with statements.
- `docs/digraph_conjecture_classification.json` — per-conjecture classification (clean
  statement, status, formalizability, definitions, reuse, missing-primitive tags,
  Rocq sketch) + the consolidated synthesis. **This is the per-conjecture source of
  truth; the tables below are its summary.**

Two conjectures are *already* stated (and proved at small parameters): AACL **Conj 5.10**
(`conjecture_5_10_at_345`) and Cheng–Keevash **Conj 1** at δ=3 (`ck_conj1_delta3`).

---

## 0. Scope

**Target = OPG digraph problems ∪ arXiv-DB digraph records, deduped** (~98 unique
conjectures from ~148 records). The 11 `problems/` folders are the **first wave** (37 of
the 148 records, ~10 papers); the remaining ~111 records come from the OPG mirror's
"Directed Graphs"/"Tournaments" subjects and 38 further arXiv papers.

**Resolved decisions (carried from v1, 2026-06-18):**
1. **Maximum coverage** — state all in-scope rows; proved ones as `Theorem`/`Example`
   targets, refuted ones (e.g. **Ádám's Conjecture** — false) as the negated proposition,
   solved ones (e.g. **PTAS-FAS** = Kenyon–Mathieu–Schudy) noted as resolved.
2. **Skip the Θ-growth envelope on the first pass** — combinatorial cores + finite
   landmarks only; **no mathcomp-analysis/reals** in the first pass (P8 deferred). A thin
   rational helper covers the few rational-fraction statements (planar `3/5`, `⌈n/r⌉`).
3. **Complexity-class statements → mathematical predicates only** — no Turing/cost model.

**New deferral lines surfaced by the full survey:**
- **P13 (flows / orientation-of-undirected)** — Jaeger, circular flow number, nowhere-zero
  / group flows, antisymmetric flows: *borderline* (these are about undirected graphs via
  an orientation, not pure digraphs) and mostly need reals. **Ship only if undirected
  interop is cheap; otherwise defer.**
- **P14 (out of scope)** — infinite / highly-arc-transitive digraphs (ends, s-arc-
  transitivity), oriented matroids, Sidorenko/graphon density, oriented Ramsey, strong
  Erdős–Hajnal, Aharoni rainbow triples: ~13 records, low reuse, each its own theory or
  outside finite MathComp. **Marked DEFERRED**; revisit only on request.

So the active target is roughly **~75 conjectures** (corpus minus P13 borderline minus
P14 deferred), of which ~30 ship **clean**, ~33 as **bounded-existential (`∃ f/m`)**
statements, and ~9 go to a **computation-model appendix** (stated as the math predicate).

---

## 1. The statement idiom

```coq
(** AACL Conjecture 5.10 — infinitely many k-ω̄-critical tournaments, for every k ≥ 3. *)
Definition conjecture_5_10_statement : Prop :=
  forall k : nat, 3 <= k -> forall N : nat,
    exists T : tournament, kcritical k T /\ (N < #|T|)%N.
(* Conjecture conjecture_5_10 : conjecture_5_10_statement.  -- optional named target *)
```

- `Definition … : Prop` introduces **no axiom**; keep any `Conjecture`/`Hypothesis`
  (an axiom) in a separate `_targets.v` so the main library stays axiom-free.
- Add cheap **sanity `Example`s** on tiny instances (`χ⃗(C3)=2`, `m 2 = 3`, the proved
  k=3,4,5 / δ=3 cases) and cross-check values against the Python oracle in `scripts/`.
- **Classes are predicates over the structure type:** "for all digraphs" =
  `forall D : diGraphType`; a forbidden class is a `pred diGraphType`; the bounded-over-
  class wrapper is `exists B : nat, forall D : diGraphType, C D -> inv D <= B` — no reals.
- Files: one `theories/conjectures/<cluster>.v` per phase-cluster, importing only the
  primitives that phase introduces. Add to `_CoqProject` after invariants/constructions.

---

## 2. Missing primitives (consolidated across the full corpus)

`unlocks` = #conjectures the primitive enables (from the classification synthesis).
Sorted by phase. The library already has the *core* (DiGraph/Oriented/Tournament,
`outdeg`/`N_out`/`N_in`, `dipath`/`dicycle`/`ell`, `strongb`, vertex orders + backedge
graph, `omegabar`, `domnum`, `kcritical`, `lexprod`, Cayley/circulant/AC,
`vertex_transitiveb`, undirected ω/χ via interop).

| Phase | Primitive | unlocks | Notes |
|---|---|---:|---|
| **P9** | **`indeg`** (+ min-outdeg / min-indeg / semidegree δ⁰) | 18 | **highest ROI**; mirror of `outdeg`; `N_in` set exists, the *count* doesn't |
| **P9** | **`girth`** (shortest dicycle; `r`-free predicate) | 10 | on top of `dicycle`+`ell`; anchors Caccetta–Häggkvist |
| **P9** | **`second-neighbourhood`** `N⁺⁺` | 3 | tiny add on `N_out`; carries Seymour's 2nd-nbhd |
| **P2** | **`dichromatic`** χ⃗ (+ 2-colour, fractional) | 24 | the hub of the heroes/Aboulker corpus; keystone |
| **P3** | **`arc-connectivity-lambda`** (k-arc-strong; κ) | 12 | SAD / branchings / Woodall / connectivity-maderian |
| **P6** | **`Forb_ind`** (induced containment + bounded-over-class) | 22 | every Gyárfás–Sumner / χ-bounded item |
| **P6** | **`oriented`** trees/forests/stars + `TT_k` + underlying functor | 16 | structured families on top of `Oriented` |
| **P9b** | **`oriented-tree-containment`** + maderian-threshold wrapper | 14 | collapses the 1610.00876 Mader cluster + Burr |
| **P9b** | **`subdivision-containment`** (TT_k, complete digraph) | 5 | arcs → internally-disjoint dipaths |
| **P10** | **`vertex-disjoint-cycle-packing`** (+ Erdős–Pósa dual) | 6 | Bermond–Thomassen, Hoàng–Reed |
| **P10** | **`branchings`** (out/in-arborescence + arc-disjoint) | 7 | Thomassen branchings, bi-trees |
| **P10** | **`dijoin-dicut`** (min dicut / dijoin) | 1 | Woodall (directed Lucchesi–Younger) |
| **P10** | **`path-partition`** (k-norm, dipath decomposition) | 4 | Linial–Berge, tournament path-decomp |
| **P4** | **`FAS`** (feedback arc set β; max-over-orientations) | 6 | distinct from `omegabar`; arc-deletion optimum |
| **P4** | **`arc-reversal`** (+ `del_arc`, `num_dicycles`) | 4 | Ádám (disproved — good negative test), FAS-via-reversal |
| **P11** | **`majority-colouring`** (+ list/fractional) | 6 | pure function on `N_out`/`outdeg`; ships clean |
| **P11** | **`oriented-chromatic`** / digraph homomorphism `dhom` | 5 | hom to a tournament; reuses Tournament/`dgiso` |
| **P11** | **`arc-colouring`** / monochromatic reachability | 4 | reuses `dipath`/`dicycle` |
| **P12** | **`planarity`** (underlying graph; genus/surface) | 7 | Two-Color, planar-3/5; via graph-theory minors |
| **P12** | **`twin-width`** (contraction-sequence red-degree) | 1 | AACL Conj 3.12 (in plan) |
| **P12** | **`tree-decomposition`** (di-treewidth, bag orthogonality) | 2 | isolated heavy-width items |
| **P8** | **`reals`** (Landau o/Ω/Θ, c^n, graphon, real thresholds) | 26 | deepest layer; ships **last**; many are P13/P14 anyway |
| **P13** | **`group/nowhere-zero/circular flow`** + chromatic index | 6 | *borderline* undirected; ship only if cheap |
| **P14** | infinite/ends, oriented-matroid, Sidorenko, Ramsey, EH | ~13 | **DEFERRED** (own theories / outside finite MathComp) |

---

## 3. Unlock map (phase dependency)

```
existing core ─┬─► P1  free wins (clique-cluster 5.10/5.9/5.8, Cheng–Keevash general)
               ├─► P9  +indeg +girth +N⁺⁺  ► Seymour-2nd-nbhd, Caccetta–Häggkvist,
               │        long-cycles-in-diregular, Jackson-Hamilton, regular degree items
               └─► P9b +tree/subdivision-containment ► Mader cluster, Burr, antidirected trees

P-acyc ─► P2 dichromatic χ⃗ ─┬─► chordal, oriented-tri-free cores, Two-Color (+P12 planar)
                            └─► (+P6) heroes, twin-width 3.12 (+P12), 2-extremal 9.2 (+P3)

P3 arc-conn λ ─► SAD/WC3/CL1 (arc_disjoint), partition-into-k-strong, (+branchings) Thomassen
P4 FAS + arc-reversal ─► path-FAS (math predicate), CSS non-edges, Ádám (¬), r-free
P6 Forb_ind + oriented-families ─► Gyárfás–Sumner(tournaments+oriented), heroes, χ-bounded
P10 packing+duality ─► Bermond–Thomassen, Hoàng–Reed, Woodall, Linial–Berge, branchings
P11 colouring variants ─► majority-colouring family, oriented-chromatic, monochromatic-reach
P12 structural width ─► Two-Color, planar-3/5, twin-width, di-treewidth
P8 reals ─► all Θ-growth / density / flow-value items  (deferred)
P13 flows (borderline) · P14 infinite/matroid/Sidorenko/Ramsey (deferred)
```

---

## 4. Phased roadmap

P0–P8 unchanged from v1 (the 11-folder spine). **P9–P14 are the corpus extension.**
Recommended order interleaves cheapest-fame-first.

- **P0 Scaffold** — `conjectures/` package, idiom, bounded-over-class wrapper, deferral
  policies. *(small)*
- **P1 Free wins** — generalise the two done conjectures + the AACL clique-cluster
  (5.10 ∀k, 5.9, 5.8, dom-cluster) and Cheng–Keevash Conj 1 general / girth / Conj 16.
  Existing machinery only. *(small)*
- **P9 Classic digraph core** ⭐ **DO RIGHT AFTER P1 — best fame:cost ratio.** Add
  `indeg`, `girth`, `second-neighbourhood`, semidegree. Ship **Seymour's Second
  Neighbourhood, Caccetta–Häggkvist** (+ bipartite variants, CSS non-edges via P4),
  long-directed-cycles-in-diregular, Jackson Hamilton, Alspach even-tournament-path-
  decomp degree side, regular/Eulerian degree conditions. ~18–21 clean statements,
  almost no structural machinery. *(medium)*
- **P2 Dichromatic core** (keystone) — `acyclic`, χ⃗, `Forb_ind` skeleton, bounded
  wrapper; ship chordal `𝒞₃`+`m(k)`, oriented-tri-free cores, heroes Conj 6.2/Thm 6.1,
  the Two-Color combinatorial core (planarity → P12). *(medium)*
- **P9b Maderian containment** — `oriented-tree/forest/star` families + subdigraph &
  subdivision containment + maderian-threshold (`∃ m`) wrapper. Collapses the 1610.00876
  Mader cluster (Conj 3/4/7/Problem 12/16), Burr's oriented-trees, antidirected trees
  into ~8 bounded-existential statements. *(medium)*
- **P3 Connectivity & SAD** — `arc-connectivity-lambda`, spanning-strong-subdigraph, SAD;
  ship Bang-Jensen–Yeo SAD, WC3, CL1, kernel-shell, partition-into-k-strong; then
  `branchings` (Thomassen out/in-branching) + arborescence sub-phase. *(medium→large)*
- **P10 Packing & duality** — `vertex-disjoint-cycle-packing`, `dijoin-dicut`,
  `path-partition` (branchings from P3). Ship **Bermond–Thomassen, Hoàng–Reed, Woodall,
  Linial–Berge**, even-tournament path-decomposition, Erdős–Pósa long cycles, the
  bi-tree/forward-cover temporalization items. *(medium)*
- **P4 FAS / degreewidth** — `FAS`, `arc-reversal`, `del_arc`, `num_dicycles`,
  degreewidth Δ\*, linear-forest, directed 3/4-cycle, transversal. Ship path-FAS
  (`has_LFO` + 3/4-cycle-transversal + matching⟺Δ*≤1 + minimal-LFO-NO-infinite),
  CSS non-edges, `r`-free, Ádám (¬, negative test). Complexity wrappers omitted. *(medium)*
- **P5 Unavoidability** — containment + `unvd` + `mad`; ship 2410.23566 Conj 9, Problem 6
  (+ the sibling Conj 7/10/11, Problems 8/12). *(medium)*
- **P6 Heroes** — `hero` predicate (Berger), `⇒`-join, `Cₖ`-substitution, oriented-
  forest/star, named small digraphs. Ship Conj 4.2/4.4/6.2, Problem 1.2, minimal-heroic-
  families, **Gyárfás–Sumner for tournaments (Conj 4.3)**, Forb(H)-χ-bounded-iff-forest
  (1605.07411 Conj 2/4/5). *(medium→large)*
- **P11 Colouring variants** — `majority-colouring` (collapses 7 records → ~3 statements),
  `oriented-chromatic`/`dhom`, `arc-colouring`/monochromatic-reachability. Ship the clean
  ones; defer circular-F-COL/fractional **complexity** items to the computation-model
  appendix. *(medium)*
- **P12 Structural width** — `planarity` (graph-theory minors), `twin-width` (AACL 3.12),
  `tree-decomposition`. Ship Two-Color, planar-3/5, AACL 3.12/3.13/3.16; defer orthogonal-
  decomposition + minor-closed-class items. *(large)*
- **P7 Heavy bespoke (from v1)** — twin-width ordered/BST (P12 overlap), the Hajós-join /
  plane-tree / H₂ / 2-extremal machinery, blow-ups (S̃ₙ, backward-blowup, k-dicritical).
  *(large)*
- **P8 Reals (deferred)** — mathcomp-analysis + Landau; the ~26 Θ-growth/density items.
  Prefer a thin **rational-fraction helper** for `3/5`, `⌈n/r⌉` so those ship earlier. *(large)*
- **P13 Flows (borderline, optional)** — nowhere-zero/group/circular flows, chromatic
  index; ship statement-only only if undirected interop is cheap. *(opt-in)*
- **P14 Deferred / out of scope** — infinite/arc-transitive digraphs, oriented matroids,
  Sidorenko/graphon, oriented Ramsey, strong-EH. *(not in this programme)*

**Sequence:** core → **P1 → P9** → P2 → P9b → P3 → P10 → P4 → P5 → P6 → P11 → P12/P7 →
P8 → (P13) → (P14). **Single highest-ROI first action after P1: add `indeg`** (dependency
of 18 conjectures; the library has `N_in` the set but not the count).

---

## 5. Corpus summary (per-conjecture detail in `digraph_conjecture_classification.json`)

| Phase-cluster | ~#conj | New primitives | Marquee / examples | Formalizability |
|---|---:|---|---|---|
| P1 free | 6 | (none) | Conj 5.10 ∀k, Q5.9, 5.8, dom-cluster, Cheng–Keevash Conj 1 | clean/bnd |
| **P9** core | ~20 | indeg, girth, N⁺⁺ | **Seymour 2nd-nbhd, Caccetta–Häggkvist**, long-cycles-diregular, Jackson | clean |
| P9b maderian | ~8 | tree/subdivision containment | every-oriented-tree-δ⁺-maderian, Burr, antidirected trees, mader_χ̄(K_n) | bnd |
| P2 dichromatic | ~10 | dichromatic χ⃗ | chordal 𝒞₃ + m(k), oriented-tri-free cores, Two-Color core | clean/bnd |
| P3 connectivity | ~12 | arc-conn λ, spanning-strong | **Bang-Jensen–Yeo SAD**, WC3, partition-into-k-strong | clean |
| P10 packing | ~10 | cycle-packing, branchings, dijoin-dicut, path-partition | **Bermond–Thomassen, Hoàng–Reed, Woodall, Linial–Berge** | clean/bnd |
| P4 FAS | ~8 | FAS, arc-reversal | path-FAS (predicate), CSS non-edges, Ádám (¬), r-free | clean (cmp\*) |
| P5 unvd | ~6 | unvd, mad | 2410.23566 Conj 9/7/10/11, Problems 6/8/12 | bnd |
| P6 heroes | ~14 | Forb_ind, oriented families, hero | **Gyárfás–Sumner tournaments**, Forb(H)-χ-bounded-iff-forest, Conj 4.2/4.4/6.2 | bnd/hard |
| P11 colouring | ~13 | majority-col, oriented-chrom, arc-col | majority-3-colouring family, oriented-χ planar, monochromatic-reachability | clean (cmp\*) |
| P12/P7 width | ~8 | planarity, twin-width, tree-decomp, Hajós/H₂ | Two-Color, AACL 3.12/3.13/3.16, **2-extremal Conj 9.2** | bnd/hard |
| P8 reals | ~26 | reals/Landau | oriented-tri-free Θ, acyclic-subgraph n^{3/4}, density forms | **deferred** |
| P13 flows | ~6 | flows, χ-index | Jaeger modular orientation, circular flow numbers | **borderline** |
| P14 out-of-scope | ~13 | — | infinite arc-transitive, oriented matroid, Sidorenko, Ramsey, EH | **deferred** |

\* `cmp` = the complexity wrapper is omitted; only the mathematical predicate ships.

**Marquee open + clean (priority flagships):** Seymour's Second Neighbourhood,
Caccetta–Häggkvist, Two-Color (Neumann-Lara), Woodall, Bermond–Thomassen, Hoàng–Reed,
Linial–Berge path-partition duality, Gyárfás–Sumner for tournaments, Forb(H)-χ-bounded-
iff-forest, Bang-Jensen–Yeo SAD.

**Notable status flags from the survey:** Ádám's Conjecture is **FALSE** (state as `¬`);
PTAS-FAS-in-tournaments is **SOLVED** (Kenyon–Mathieu–Schudy); Bermond–Thomassen and the
edge-disjoint-Hamilton-in-tournaments item are **partial**. ~13 records are open-ended
classifications (only the characterised predicate is statable, not a single goal).

---

## 6. Open decision

The only remaining fork is whether to spend effort on **P13 (flows / orientation-of-
undirected, ~6 items)** — they are borderline (about undirected graphs) and mostly need
reals — and whether **P14 (~13 infinite/matroid/Sidorenko/Ramsey items)** should stay
deferred. Default: **defer both**; the active programme is P0–P12 (~75 conjectures,
~30 clean + ~33 bounded-existential + ~9 computation-model-appendix).

---

## 7. Dependency graph of conjectures (implications as Rocq proofs)

Second deliverable: a graph whose **nodes are conjecture statements** and whose **edges
are machine-checked implications** `A ⟹ B`. An edge is a *relative* theorem — provable
**without** resolving either conjecture:
```coq
Theorem conj_5_10_implies_neg_Q5_9 :
  conjecture_5_10_statement -> ~ question_5_9_statement.
Proof. ... Qed.
```
So this layer is genuine `Qed`-closed content (unlike the `_statement` definitions).

### 7.1 Design consequence — factor statements for derivability (affects P0–P2)
Edges must type-check, so statements must share granularity from the start:
- a special case must be the general statement **instantiated** (`conj1_at_delta3 :=
  conj1_statement` applied to 3) → the edge is `fun H => H 3 …`;
- ONE shared definition per recurring notion (`χ⃗`, `unvd`, `omegabar`, `Forb_ind`) — never
  two encodings of "the same" notion, or implications between them are unprovable;
- phrase weakenings (`∃ f` vs `f = id`; the `dom ≤ ω̄ ≤ dic` sandwich) so the strengthening
  visibly implies the weakening.

### 7.2 Edge types
`implies` (`A -> B`), `equiv` (`A <-> B`), `specializes` (B = A instantiated),
`refutes` (A known false → record the proved `~ A_statement`, e.g. Ádám, and any `¬A ⟹ C`),
`joint` (`A -> B -> C`, two-premise / AND-node).

### 7.3 External lemmas — stay axiom-free
Some literature implications use a cited theorem Z not in the library. Do **not**
`Admitted`/axiomatize. Keep Z as a `Definition Z_statement : Prop` in
`conjectures/external.v` and carry it as an explicit hypothesis:
```coq
Theorem conj_3_16_implies_3_12 :
  geniet_thomasse_bst_tww_statement ->     (* cited Thm 3.15, as a hypothesis *)
  conj_3_16_statement -> conj_3_12_statement.
```
Honest, `Qed`-closed, dependency greppable; drop the hypothesis if Z is later proved.

### 7.4 The graph as an artifact
- **Layer:** `theories/conjectures/implications/<theme>.v`, each edge a
  `Theorem <src>_implies_<dst> … Qed.` under a fixed naming convention.
- **Extraction:** a script scans `_implies_`/`_equiv_` theorems → `docs/dependency_graph.json`
  → render via the existing `site/`.
- **Optional elegant upgrade:** reflect the graph INTO the library as a `diGraphType` whose
  vertices are a `conj_id` enum and whose arcs are exactly the proved edges — *the
  dependency graph of digraph conjectures, itself a digraph in the library*, kernel-checked.

### 7.5 Seed edges (real, literature-stated, provable as relative theorems)
- Conj 5.10 ⟹ ¬Q5.9 ; Q5.9 ⟹ Conj 5.8 ⟹ dom⇒ω̄-cluster (via `dom ≤ ω̄`).
- Conj 3.16 ⟹ Conj 3.13 ⟹ Conj 3.12 (Thm 3.15/3.14 as external hypotheses).
- Cheng–Keevash girth-g (strong) ⟹ Conj 1 (g=3) ; Conj 1 ⟹ Conj 1@δ=3 (instantiate).
- unvd Conj 9 ⟹ Conj 11 (and ⟹ Conj 10 with Sumner) [paper-stated].
- oriented-tri-free Conj 3 ⟹ Conj 4 [paper-stated].
- heroes Conj 4.2 ⟹ Conj 4.4 (H transitive) ; Forb-χ-bounded Conj 2 ⟹ Conj 4 (oriented-
  star special case) ; Problem 1.2 ⟹ {4.2, 4.4} once a candidate characterization is fixed.
- 2-extremal Conj 9.2 ⟹ Conjecture-P (planar) and ⟹ the 3-connected case.
- Caccetta–Häggkvist general ⟹ CH-triangle (r = n/3 instance).

### 7.6 Discovery scope
The reliable, high-value edges are **what the papers themselves assert** ("X implies Y",
"special case", "weakening") — already partly captured in
`digraph_conjecture_classification.json` (`duplicate_of` + notes). Recommended: mine those
as the **spine** + opportunistic cross-paper specializations. *Exhaustively discovering
every true implication among ~98 statements is itself a research problem* — out of scope
unless requested.

### 7.7 Plan impact
P0 gains: `external.v` (cited-result hypotheses), the edge naming convention, the
extraction+render script. Every phase gains an **implications sub-step**: whenever two
related statements both exist, add their edge in the same phase. The graph then grows
monotonically with the statements and is complete (for the literature spine) when they are.
