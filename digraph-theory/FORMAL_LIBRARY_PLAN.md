# A MathComp-based graph-theory library — design plan

**Status:** v1.2 (2026-06-11) — **all milestones M0–M6 complete: the k = 5 theorem
(`applications/k5/main.v`) is fully formalized and axiom-free.** Earlier revision
history: v1.1 after installing and inspecting the actual
toolchain (opam switch `digraph`: Rocq 9.1.1, MathComp 2.5.0, mathcomp-classical 1.16.0,
HB 1.10.2, coq-graph-theory 0.9.7). Decisions D1, D2, D3, D6, D7 are now resolved (§10);
milestone M0 is done. The paper and the exact Python oracle are vendored in `paper/` and
`scripts/`.
**First concrete goal:** formalise `paper/k5_theorem.tex` — an infinite family of
`5`-`ω̄`-critical tournaments `AC_n[AC_n]` (Aboulker–Aubian–Charbit–Lopes Conj. 5.10 at
`k=5`).
**Strategic goal:** build the directed/tournament layer *and its invariant theory* in a
way general enough to grow into a full graph-theory library that others can build on.
**Audience:** mathematicians. Classical logic is acceptable (`mathcomp-classical`); no
constructivity constraint.

---

## 1. Executive summary of the ecosystem survey

Verified against current sources (June 2026). Provenance URLs in §11.

| Need | Already exists? | Verdict |
|---|---|---|
| Undirected clique number `ω`, independence `α`, chromatic `χ`, coloring, Weak Perfect Graph Thm | **Yes** — `coq-graph-theory` `core/coloring.v` (`omega_mem`, `alpha_mem`, `chi_mem`, `clique`, `cliques`, `maxcliques`) | **Reuse** |
| Simple graphs, induced subgraph, complement, connectivity, Menger, matching, Hall/König, minors, treewidth | **Yes** — graph-theory `sgraph.v`, `connectivity.v`, `minor.v`, `treewidth.v` | **Reuse** |
| Directed graph type | **Partly** — graph-theory `digraph.v`: `diGraph` = `finType` + a bare `rel`; only `connect`/paths | **Reuse the type, extend the theory** |
| Domination number | **Undirected only** — graph-theory `dom.v` is `sgraph`-based (verified in 0.9.7 sources); its generic `hereditary`/`superhereditary` set combinators are reusable | **Build the directed notion; reuse combinators (D3 resolved)** |
| **Tournaments** (irreflexive + total/asymmetric-complete) | **No** | **Build** |
| **`ω̄` = min over vertex orders of `ω`(backedge graph)** | **No** | **Build** |
| **Dichromatic number `χ̄`**, χ-boundedness vocabulary | **No** | **Build** |
| **Lexicographic substitution `S[H]`** (and digraph products generally) | **No** | **Build** |
| **Cayley / circulant graphs** over a finite group / `'Z_n` | **No** (mathcomp `fingroup`/`action` give the group; the Cayley graph is a one-liner you write) | **Build (small)** |
| **Vertex-transitivity** via automorphism group action | **No graph-specific layer** (mathcomp `action`/`{perm}`/orbits exist) | **Build (thin)** |
| `'Z_n` ring, `{perm V}` orderings, `\min`/`arg min` over a finType, group actions | **Yes** — mathcomp `zmodp`, `perm`, `bigop`, `fingroup`/`action` | **Reuse** |
| Classical logic + sets over arbitrary types | **Yes** — `mathcomp-classical` (`boolp`, `classical_sets`) | **Reuse** |
| Graphs over infinite/arbitrary vertex types | `{fset T}` via `coq-mathcomp-finmap`; `set T` via classical | **Reuse as the "general" seam** |

**Bottom line.** ω/χ/cliques on *undirected, finite* graphs are solved — we stand on
graph-theory. Everything *directed and tournament-specific* — including the entire
ω̄/criticality/substitution/circulant apparatus the paper needs — is greenfield. The
library's identity is therefore: **the directed-and-tournament companion to
`coq-graph-theory`, with a reusable invariant theory.**

---

## 2. Design principles

1. **Reuse, don't fork.** Depend on `coq-graph-theory` for undirected `ω`/`χ`/`clique`
   and on mathcomp for `'Z_n`/`{perm}`/`action`. The backedge graph *is* an `sgraph`, so
   `ω̄` is *defined* through graph-theory's `omega_mem` — we never reimplement clique
   search. This both saves work and makes our results interoperate with anything built on
   graph-theory.
2. **Our own HB hierarchy; record *glue* toward graph-theory (D7, resolved).**
   Inspection of graph-theory 0.9.7 shows `diGraph`/`sgraph` are *plain telescope
   records*, deliberately not packed structures (their sources note coercion-automation
   breakage), so the original sketch `HB.mixin ... of DiGraph V` cannot attach to their
   type. Decision: build our *own* HB hierarchy — `DiGraph` (finite type + arc relation)
   → `Tournament` (irreflexive + total) — so the library is extensible by others
   (weighted, oriented, loopless-multigraph siblings), and consume graph-theory through
   explicit *projections into their records* (`to_diGraph : ... -> GraphTheory.diGraph`,
   `backedge ... : sgraph`). All glue lives in `core/digraph.v` and the interop file, so
   any coercion friction stays localised. Match mathcomp naming and packaging conventions
   so it reads like part of the ecosystem.
3. **Separate the *relation* from *finiteness*.** Keep the digraph operations
   (converse, induced sub-digraph, deletion, products, Cayley) defined at the
   relation level, parametric in the vertex type, and introduce finiteness only where an
   invariant genuinely needs to enumerate (`ω̄` = min over orders, counting). This is the
   seam that lets the same definitions later extend to infinite/`{fset}`/`set`-supported
   graphs (the "all graph theory" ambition) without rewriting the core.
4. **Classical by default.** Use `mathcomp-classical` (`boolp`) so statements read like
   ordinary mathematics (EM, propositional/functional extensionality, choice). Use
   `classical_sets.set T` for the general-vertex-type seam; use mathcomp `{set T}` /
   `{fset T}` for the finite computational core.
5. **Every concrete theorem is also a stress-test of the general API.** The k=5 result is
   the first *client* of the library, kept in its own sub-package, so that "did we design
   the general layer right?" is answered continuously, not at the end.

---

## 3. Dependencies, tooling, packaging

**Toolchain floor** (matches the current ecosystem): Rocq/Coq ≥ **8.19**, MathComp ≥
**2.5.0**, Hierarchy Builder ≥ **1.5.0**.

**Installed** (opam switch `digraph`, linked to the repo via `opam switch link`,
2026-06-11): Rocq **9.1.1** (+ `coq` 9.1.1 compat metapackage), MathComp **2.5.0**
(ssreflect/algebra/fingroup), mathcomp-classical **1.16.0**, HB **1.10.2**,
coq-graph-theory **0.9.7** (pulls finmap 2.2.2). Smoke-checked: `make` builds the
prelude; `From GraphTheory Require Import preliminaries sgraph coloring.` loads and
exposes `omega_mem`/`clique`.

**opam dependencies:**
- `rocq-mathcomp-ssreflect` (+ `-algebra`, `-fingroup`) — core, `zmodp`, `perm`, `action`.
- `rocq-mathcomp-classical` (≥ 1.16) — classical logic + `set T`. *Standalone; does not
  pull in analysis.*
- `coq-graph-theory` (≥ 0.9.7) — undirected `ω`/`χ`/`clique`/`sgraph`. **D1 resolved:**
  hard dependency on `coq-graph-theory` core (not `-planar`), behind the single
  `foundations/interop_graph_theory.v` so a future swap is localised. Already installed
  in the switch; becomes a build/opam dependency when the interop file activates at M1.
- `coq-mathcomp-finmap` (≥ 2.2.2 — already pulled in by graph-theory) — *optional* for
  us, only when the infinite-vertex seam is activated. Not needed for k=5.

**Build:** `coq_makefile` via the standard rocq-community `Makefile` + `_CoqProject`
pattern (as scaffolded — simplest editor/`.vo` story; a Dune build can be added later if
a client needs one). Scaffold follows **`rocq-community/templates`** conventions
(`meta.yml` kept in sync by hand). CI: docker-coq-action on
`mathcomp/mathcomp:2.5.0-rocq-prover-9.1` (tag verified on Docker Hub; matches the local
switch), installing `rocq-mathcomp-classical` in `before_script` (+ `coq-graph-theory`
from M1).

**Naming:** ship dual opam files — primary `rocq-<name>`, compat alias `coq-<name>` —
mirroring how mathcomp core/classical/finmap now do it. **D2 resolved:** logical
namespace **`Digraph`** (`From Digraph Require Import ...`), packages
`rocq-digraph-theory` + `coq-digraph-theory`, as scaffolded.

---

## 4. Repository / module layout

Namespace `Digraph.` (D2). Lowercase, mathcomp-style filenames (matching the scaffold).
Files are grouped by layer; lower layers never depend on higher ones. Everything Rocq
lives under `theories/` so the single `-R theories Digraph` mapping covers the
application too.

```
theories/
  foundations/
    prelude.v            -- re-exports, notation, classical setup (boolp), small lemmas
    interop_graph_theory.v
                         -- the ONLY file that imports coq-graph-theory; re-exports
                            omega/alpha/chi/clique under our names; isolates the dep (D1)
  core/
    digraph.v            -- our HB DiGraph structure (finite vertex type + arc rel, D7);
                            projection to graph-theory's diGraph record; converse,
                            sub-digraph, vertex/arc deletion, induced, isomorphism
    tournament.v         -- HB structure: irreflexive + total (exactly one of u->v,v->u).
                            beats-relation, out/in-neighbourhoods N+ / N-, dominators
    order.v              -- vertex orders as {perm V} (read through enum_rank : V ≅ 'I_n);
                            backedge graph T^p : sgraph (symmetric+irreflexive by
                            construction); backedge clique = clique of T^p
  invariants/
    omegabar.v           -- ω̄(T) := min over {perm V} of ω(T^p)   [via arg min]
                            monotonicity under induced sub-digraph / deletion;
                            ω̄(C3)=2; ω̄(transitive)=1
    domination.v         -- DIRECTED domination number (defined here — graph-theory's
                            dom.v is undirected-only; reuse its hereditary combinators);
                            dom ≤ ω̄ (paper Property 3.2)
    dichromatic.v        -- χ̄(T); ω̄ ≤ χ̄; vocabulary for χ-boundedness (forward-looking)
    critical.v           -- k-ω̄-critical; criticality lemmas; deletion behaviour
  constructions/
    product.v            -- lexicographic substitution S[H] (general digraph product);
                            it is a tournament when S,H are; arc characterisation
    cayley.v             -- Cayley digraph Cay(G,S) for a finite group G, connection set
                            S; tournament iff S partitions G\{e} into S ⊍ (-S)
    circulant.v          -- specialisation to G = 'Z_n; AC_n = Cay('Z_n, g)
    automorphism.v       -- Aut(D) ≤ {perm V}; group action; vertex_transitive predicate
  invariants_advanced/
    substitution.v       -- ω̄(S[H]) ≥ ω̄(S)+ω̄(H)-1  (paper Prop "Substitution lower bound")
    transitive.v         -- vertex-transitive ⇒ ω̄(T - v) independent of v; criticality
                            reduces to a single deletion
  applications/
    k5/                  -- the target theorem; depends on everything above, nothing on it
      acn_arc_facts.v    -- Lemma "Arc-facts" (i)-(iii); g = {1..m-1} ∪ {m+1}; tournament
      acn_base.v         -- ω̄(AC_n)=3, unique triangle {0,m,2m}, autocorrelation lemma,
                            3-ω̄-critical (Prop "Facts about AC_n")
      in_neighbourhood.v -- Lemma H17 (common in-neighbourhood lies in one band)
      cells.v            -- the 8 cells, "one vertex per cell", band caps
      obstructions.v     -- the 20 infeasible cell-sets (triples / quadruples / squares)
      coverage.v         -- (b): every 5-subset of the 8 cells contains one of the 20
                            [finite, n-independent → by reflection/vm_compute (D6)]
      main.v             -- ω̄(T)=5, ω̄(T-(0,0))≥4 and ≤4, 5-ω̄-critical; Conj 5.10 @ k=5;
                            Question 5.9 fails @ k=5
  test/                  -- regression: small tournaments, oracle cross-checks
paper/
  k5_theorem.{tex,pdf}   -- the target theorem (vendored from graph-conjectures)
scripts/
  core.py, oracle.py,    -- the EXACT Python oracle for ω̄ (needs networkx; tests need
  constructions.py,         pytest). Smoke-checked in-repo: ω̄(C3)=2, ω̄(TT4)=1.
  test_oracle.py            Run: uv run --with networkx,pytest python -m pytest scripts/
```

---

## 5. Key representation decisions (with sketches)

These are *illustrative signatures*, to be refined against the actual graph-theory and
mathcomp APIs during M1.

**Digraph (our HB structure, D7) + projection.** graph-theory's `diGraph` is the plain
record `Record relType := RelType { rel_car :> finType; edge_rel : rel rel_car }` (with
`diGraph`/`DiGraph` as notations for it) — *not* an HB structure. We therefore root our
own hierarchy and project into their record world at the consumption point:
```coq
(* illustrative — exact mixin split pinned in M1 *)
HB.mixin Record HasArc V of Finite V := { arc : rel V }.
#[short(type="diGraphType")]
HB.structure Definition DiGraph := { V of HasArc V & Finite V }.

Definition to_GT (D : diGraphType) : GraphTheory.diGraph := DiGraph (@arc D).
Definition converse (D : diGraphType) : diGraphType := (* V with [rel x y | arc y x] *) ...
```
Operations (`converse`, `induced`, deletion, products, Cayley) stay at the relation
level; the general (infinite) seam keeps the same names over `V : Type` with `e : rel V`
(or `V -> V -> Prop` classically); finiteness is added only downstream. (Seam is
*designed now, implemented later* — D4.)

**Tournament (HB structure on top of ours).**
```coq
HB.mixin Record DiGraph_IsTournament V of DiGraph V := {
  arc_irrefl : irreflexive (@arc V);
  arc_total  : forall x y : V, (x != y) = arc x y (+) arc y x  (* exactly one *)
}.
#[short(type="tournament")]
HB.structure Definition Tournament := { V of DiGraph_IsTournament V & DiGraph V }.
```
Then `N+ x := [set y | arc x y]`, `N- x := [set y | arc y x]`, `beats x y := arc x y`.

**Order = permutation.** A total order of `V` is `p : {perm V}` read as the linear order
`u ≺_p v := enum_rank (p u) < enum_rank (p v)` (through the canonical `V ≅ 'I_#|V|`). The
**backedge graph** of `T` under `p` is a graph-theory `sgraph`; its constructor
`SGraph` takes the symmetry and irreflexivity *proofs*, which hold by construction of
the symmetrised backedge relation:
```coq
Definition backedge_rel (T : tournament) (p : {perm T}) : rel T :=
  [rel u v | (u ≺_p v) && arc v u || (v ≺_p u) && arc u v].  (* arc points "backward" *)
Definition backedge T p : sgraph := SGraph (backedge_sym T p) (backedge_irrefl T p).
```
A backedge clique is exactly a `clique` (graph-theory) of `backedge T p`.

**ω̄ via `arg min`, on the subset-relative ω.** Two facts verified against the installed
sources. (a) mathcomp's finType extremum is `[arg min_(p < p0 | P) F]` (with `arg_minnP`)
— use it rather than `\min_`, which has no identity over `nat`. (b) graph-theory's clique
number is *subset-relative*: `omega_mem : mem_pred G -> nat` gives `ω(A)` for
`A : {set G}` inside a fixed graph `G`, with monotonicity `sub_omega : A ⊆ B -> ω(A) ≤
ω(B)` already proved. So:
```coq
Definition omegab_at (T : tournament) (p : {perm T}) : nat := ω([set: backedge T p]).
Definition omegabar  (T : tournament) : nat :=
  omegab_at T [arg min_(p < (1%g : {perm T})) omegab_at T p].
```
`{perm V}` is a nonempty finType (identity), so the argmin is well-defined. For deletion
/ induced sub-tournaments, prefer phrasing intermediate lemmas as `ω(A)` for subsets `A`
of one *fixed* backedge graph (free monotonicity via `sub_omega`), bridging to the
induced sub-tournament's own backedge graph once, via "an order on `V` restricts to an
order on any subset". **This is the single most load-bearing definition — pin it in M1
and cross-check against `scripts/core.py`'s oracle on `C3`, `S̃₃`, `n≤7`.**

---

## 6. General theory to build (reusable, not k5-specific)

These are the lemmas that make the library worth depending on, each stated for *all*
tournaments / digraphs:

- **`OmegaBar`:** `ω̄` well-defined; `ω̄(T) ≤ ω̄(T')` for `T` induced in `T'`;
  `ω̄(C3)=2`, `ω̄(TTₙ)=1`; `ω̄(T - v) ∈ {ω̄(T), ω̄(T)-1}` (deletion drops by ≤1).
- **`Domination`:** `dom(T) ≤ ω̄(T)` (paper Property 3.2) — the lower-bound engine.
- **`Substitution`:** `ω̄(S[H]) ≥ ω̄(S)+ω̄(H)-1` for all `S,H`. The paper's proof
  (block reps + promote the source block to a full `ω̄(H)`-clique) is a clean, general,
  *first marquee theorem* of the library — worth doing carefully and reusing.
- **`Transitive`:** if `Aut(T)` acts transitively on `V`, then `ω̄(T - v)` is independent
  of `v`; hence `k`-criticality reduces to a single deletion. General and broadly useful.
- **`Cayley`/`Circulant`:** `Cay(G,S)` is a tournament iff `S ⊍ (-S) = G\{e}`; translation
  by `G` is an automorphism (so Cayley tournaments are vertex-transitive). Specialise to
  `'Z_n`.
- **`Product`:** arc characterisation of `S[H]`; closure of "is a tournament" under `[·]`;
  associativity sufficient for `AC_n[AC_n]`.

Doing these *generically* is exactly the "build for others" requirement — the k=5 file
then reads as a short application.

---

## 7. The target theorem, decomposed

Mapping `paper/k5_theorem.tex` to modules (paper labels in parentheses):

1. **`ACn_arc_facts` (Lemma 1, arc-facts).** `g = {1,…,m-1} ∪ {m+1} ⊆ 'Z_n`,
   `n = 2m+1`. `AC_n` is a tournament (vertex-transitive). Residue facts (i)–(iii).
   *Parametric in `n`* → real proofs over `'Z_n` with `modn`/interval reasoning.
2. **`ACn_base` (Prop "Facts about AC_n").** `ω̄(AC_n)=3`; unique backedge triangle
   `{0,m,2m}`; the interval-**autocorrelation lemma** `minₜ |N₀ ∩ (N₀+t)| = 2`; via
   `dom ≤ ω̄` get the lower bound; `ω̄(AC_n - v)=2`, so `AC_n` is `3`-`ω̄`-critical.
3. **`Substitution` (general, §6)** gives `ω̄(T) ≥ 5` for `T = AC_n[AC_n]`, and
   `ω̄(T-(0,0)) ≥ 4` via `(AC_n-0)[AC_n]` + monotonicity.
4. **Upper bounds (the hard core).** `ω̄(T) ≤ 5` and `ω̄(T-(0,0)) ≤ 4`:
   - `InNeighbourhood` (Lemma H17): common in-neighbourhood of an `H`-vertex and an
     `L`-vertex lies in a single band. *Parametric.*
   - `Cells`: order survivors by `key=(c(b),c(a),a,b)`; "no backedge inside a cell"
     (Lemma "cell") ⇒ a backedge clique injects into the 8 cells; band caps `n₁,n₂≤3`,
     `n₃≤2`. *Parametric (uses arc-facts).*
   - `Obstructions`: the 20 infeasible cell-sets — ten triples (5 mirror pairs), four
     outer-source quadruples, six squares — each refuted by arc-facts + H17. *Parametric
     but finite casework.*
   - `Coverage` (b): every 5-subset of the 8 cells contains one of the 20 — `binom(8,5)=56`
     purely combinatorial, **`n`-independent ⇒ prove by reflection/`vm_compute`** over an
     explicit `{set 'I_8}` enumeration. This is the one place to lean on computation.
5. **`Main`.** Assemble: `ω̄(T)=5` (§3 value), `ω̄(T-(0,0))=4` (3+4), and by
   `Transitive` + vertex-transitivity of `T`, `ω̄(T-v)=4` for all `v`. Conclude
   `5`-`ω̄`-critical; infinite family (distinct order `n²`); **Conj 5.10 @ k=5**;
   **Question 5.9 fails @ k=5** (monotonicity corollary).

**Hardest parts (budget accordingly):** the parametric residue arithmetic over `'Z_n`
(arc-facts, H17, autocorrelation) and the 20-set casework. The casework is *finite and
`n`-independent in structure* but each case still mixes a parametric arc-fact with a small
logical refutation — expect this to dominate the effort. Keeping arc-facts as clean,
reusable rewrite lemmas is the key to making the 20 cases short.

---

## 8. Roadmap / milestones

Each milestone is independently useful and ends with green CI + a tagged checkpoint.

- **M0 — Scaffold. ✅ Done (2026-06-11).** rocq-community-style scaffold, `coq_makefile`
  build, dual opam, CI on the matching docker image, `prelude`, dedicated opam switch
  `digraph` with all deps (incl. graph-theory) installed; paper + Python oracle vendored.
  *Exit met:* `make` builds the prelude in the pinned switch; GraphTheory imports
  smoke-checked; oracle runs in-repo.
- **M1 — Core + ω̄. ✅ Done (2026-06-11).** Interop activated (with the `ω(K2)=2` smoke
  check and generic ω lemmas incl. `omega_hom`); `digraph` (own HB hierarchy per D7,
  sub-digraphs as canonical instances on subtypes), `tournament` (+ 3-cycle dichotomy,
  examples C3/TTₙ), `order` (`ltp`, the order-realization theorem + pullback — the
  workhorse), `omegabar` (arg-min definition, ω̄=1 ⟺ transitive, monotonicity via
  arc-preserving embeddings, iso-invariance), `critical`. *Exit met, axiom-free:*
  `ω̄(C3)=2` (`omegabar_C3`), `ω̄(TTₙ)=1` (`omegabar_TT`), C3 is 2-ω̄-critical
  (`C3_kcritical2`) and unique up to iso (`kcritical2_card3`, `kcritical2_uniq`);
  values cross-checked vs the Python oracle. *Lesson (D6):* `vm_compute` does NOT
  reduce through the abstract definitions (mathcomp's `enum` is locked) — the M6
  `coverage.v` reflection check must use a purpose-built computational model, not
  the abstract ω̄.
- **M2 — Constructions. ✅ Done (2026-06-11).** `automorphism` (`dgaut` group,
  `vertex_transitiveb`), `product` (`lexprod` + tournament closure + arc
  characterization), `cayley` (tournament iff `A ⊎ A⁻¹ = G\{1}`; translations are
  automorphisms; vertex-transitive), `circulant` ('Z_n group ops are additive
  *definitionally*, so circulants = Cayley; `ACset_cond` residue argument). *Exit met,
  axiom-free:* `AC m` is a canonical tournament on `2m+1` vertices (`m := m'.+1` keeps
  instances hypothesis-free), vertex-transitive via translations; `S[H]`
  tournament-closed. Cross-checked vs the oracle (AC₃/AC₅/AC₇ tournaments, ω̄(AC₇)=3,
  lex-closure).
- **M3 — General invariants. ✅ Done (2026-06-11).** `substitution`
  (`omegabar_lexprod_ge`: ω̄(S)+ω̄(H) ≤ ω̄(S[H])+1, via block-min representatives +
  promote-the-last-block, with reusable edge correspondences `cross_edgeE`/
  `block_edgeE`), `transitive` (`omegabar_del_vt`, `vt_kcritical`; demo
  `AC_del_uniform`), `domination` (`domnum_le_omegabar` via the greedy ≺-min chain
  `greedy_clique_dom`). *Exit met, axiom-free; bounds oracle-checked tight
  (dom(C3)=ω̄(C3)=2, ω̄(AC₃[AC₃])=3=2+2−1).* **The library is now publishable/usable on
  its own.**
- **M4 — AC_n base. ✅ Done (2026-06-11).** `acn_arc_facts` (value arithmetic,
  gap characterizations `AC_arc_lt`/`AC_arc_gt`, band facts (i)–(iii)),
  `acn_base` (`omegabar_AC`: ω̄(AC_n)=3 via 3-bucket pigeonhole up / domination +
  autocorrelation `autocorr2` down; `omegabar_AC_del`: ω̄(AC_n−v)=2;
  `AC_kcritical3`), all for m ≥ 3, axiom-free, oracle-checked (AC₇/AC₉). *Exit
  met* — with one conscious deviation: the "unique triangle {0,m,2m}" clause is
  not separately formalized; criticality is proved directly by the 2-bucket
  argument on AC_n−0, which subsumes the clause's only use.
- **M5 — Substitution value + lower deletion. ✅ Done (2026-06-11).**
  `applications/k5/k5_lower.v`: `omegabar_T_ge5` (ω̄(ACₙ[ACₙ]) ≥ 5 = 3+3−1 via the M3
  substitution bound + M4 values) and `omegabar_Tdel_ge4` (ω̄(T−(0,0)) ≥ 4 via the
  embedding (ACₙ−0)[ACₙ] ↪ T−(0,0) and 2+3−1). *Exit met, axiom-free.* The M3/M4
  groundwork made this a ~90-line file — exactly the "general theory pays off"
  design bet.
- **M6 — Upper bounds (the casework). ✅ Done (2026-06-11).**
  `in_neighbourhood.v` (Lemma H17 via the in-window/dichotomy bounds),
  `cells.v` (bands, the 9 cells, the radix key order `qk` as a real `{perm T5}`,
  the cell Lemma `cidx_inj_clique`, occupancy count), `obstructions.v` (all 20
  cell-sets refuted from arc-facts + H17; `no_obstruction`), `coverage.v` (the
  256-case boolean coverage check `coverage5` — the planned n-independent
  computational step, by exhaustive `case`), `k5_upper.v` (`ω̄(T) ≤ 5`,
  `ω̄(T−(0,0)) ≤ 4`; key order pulled back along `val` for the deletion), and
  `main.v` (`ω̄(T) = 5`, `ω̄(T−v) = 4` for all v via `lexprod_vertex_transitive`
  added to `product.v`, `T5_kcritical5`, `card_T5 = n²`,
  `conjecture_5_10_at_k5`, `proper_sub_omegabar_le4`,
  `question_5_9_fails_at_k5`). *Exit met, all 9 exit theorems axiom-free.*
  **The formalization of `paper/k5_theorem.tex` is complete.**

A natural *first public release* is end of **M3** (the reusable directed/tournament
theory), with the k=5 application following as a showcase paper/section.

---

## 9. How this grows into "all graph theory"

The design choices that keep the door open:
- **HB structure hierarchy** rooted at a relation, so undirected (`sgraph`, via
  graph-theory), directed (`diGraph`), tournament, and future variants (oriented,
  weighted, multigraph) are siblings/refinements others can add without touching the core.
- **Relation-level operations + isolated finiteness** (§2.3) → the same `converse`,
  `induced`, `product`, `Cayley` definitions extend to `{fset}`/`set`-supported infinite
  graphs when that seam is activated, rather than being re-derived.
- **Invariant vocabulary** (`ω̄`, `χ̄`, domination, criticality, χ-boundedness scaffolding
  in `Dichromatic.v`) is the natural home for the broader programme
  (Aboulker et al., dichromatic number, χ-boundedness) the group is already working on
  — these reuse the exact same `arg min`-over-orders / coloring machinery.
- **Interop, not fork** with graph-theory means anything proved there (treewidth, minors,
  Menger, WPGT) is immediately available to clients of this library.

---

## 10. Decisions (status as of 2026-06-11)

- **D1 — graph-theory dependency. ✅ RESOLVED:** hard dependency on `coq-graph-theory`
  core behind `foundations/interop_graph_theory.v`. Installed (0.9.7) in the switch and
  verified coinstallable with the rest of the stack; activates in `_CoqProject`/opam at
  M1.
- **D2 — name & namespace. ✅ RESOLVED:** logical namespace `Digraph`, packages
  `rocq-digraph-theory` / `coq-digraph-theory` (as scaffolded).
- **D3 — domination reuse. ✅ RESOLVED (define our own):** graph-theory `dom.v` is
  undirected-only (`Variable G : sgraph` throughout — verified in the 0.9.7 sources); the
  paper needs *directed* domination on tournaments. We define it in
  `invariants/domination.v`, reusing `dom.v`'s generic `hereditary`/`superhereditary`
  combinators where convenient.
- **D4 — infinite-vertex seam now vs later.** *Open (recommendation unchanged):* design
  the relation layer parametrically now, implement the `{fset}`/`set` instantiation only
  when a client needs it (not for k=5). Keeps M1–M6 finite and fast.
- **D5 — order representation.** *Open (pin in M1):* `{perm V}` (recommended; nonempty
  finType, clean `arg min`) vs. injections `V -> 'I_#|V|` vs. mathcomp `order` structures
  (rejected: not enumerable).
- **D6 — computation policy. ✅ RESOLVED:** `vm_compute`/proof-by-reflection is allowed
  for finite, `n`-independent checks — the `coverage.v` 56-case check is the intended
  use. The kernel still checks everything; no axioms involved.
- **D7 — structure style (new). ✅ RESOLVED:** our own HB hierarchy (`DiGraph` →
  `Tournament`), with explicit projections into graph-theory's plain records
  (`to_GT`, `backedge : ... -> sgraph`) at the consumption boundary. Rationale: their
  records cannot host HB mixins, and HB on our side keeps the library extensible by
  others; glue is localised to `core/digraph.v` + the interop file. Risk to watch in M1:
  coercion friction between our `Tournament.sort` and their `rel_car` faces — if it
  bites, the fallback is plain telescope records mirroring graph-theory.

## 11. Provenance (sources checked, June 2026)

- coq-graph-theory: `github.com/coq-community/graph-theory` (→ `rocq-community`),
  `theories/core/{digraph,sgraph,coloring,connectivity,minor,treewidth,dom}.v`; v0.9.7,
  mathcomp ≥ 2.5.0, HB ≥ 1.5.0.
- mathcomp core (reorg `boot/`, `algebra/`, `order/`, `finite_group/`; dual `coq-`/`rocq-`
  opam): `github.com/math-comp/math-comp`, tag mathcomp-2.5.0; `fingraph`, `zmodp`,
  `perm`, `action`, `bigop` (incl. `arg min`), `order`.
- mathcomp-classical: `github.com/math-comp/analysis/tree/master/classical`
  (`boolp.v` = prop-ext + dep fun-ext + `cid` ⇒ EM; `classical_sets.v` = `set T` over
  arbitrary `T`); `coq-mathcomp-classical` 1.16.0; standalone (no analysis dep).
- finmap: `github.com/math-comp/finmap`; `coq-mathcomp-finmap` 2.2.3 (`{fset}`, `{fmap}`
  over `choiceType`).
- Tournaments / `ω̄` / `χ̄` / χ-boundedness / lexicographic substitution / Cayley graphs:
  **no existing mathcomp-ecosystem formalisation found** (greenfield).
- Tooling: `rocq-community/templates` (`meta.yml`), `coq_makefile` build, dual
  `rocq-`/`coq-` opam naming; Rocq/Coq ≥ 8.19.
- Target: `paper/k5_theorem.tex`; oracle cross-check `scripts/core.py`, `scripts/oracle.py`
  (vendored from `~/Recherche/graph-conjectures/problems/tournament_clique_number_omega_cluster/`).

**Verified against the installed switch (2026-06-11):**
- opam switch `digraph`: Rocq 9.1.1, MathComp 2.5.0, mathcomp-classical 1.16.0,
  HB 1.10.2, coq-graph-theory 0.9.7, finmap 2.2.2; `make` builds the prelude.
- graph-theory 0.9.7 sources inspected: `diGraph`/`sgraph` are plain telescope records
  (digraph.v:405, sgraph.v:14), NOT HB structures (→ D7); `omega_mem`/`alpha_mem`/
  `chi_mem`/`clique`/`cliques` exist as assumed and are subset-relative with `sub_omega`
  monotonicity (coloring.v); `dom.v` is sgraph-only (→ D3); `induced` exists for both
  `diGraph` and `sgraph`; `SGraph` constructor takes symmetry+irreflexivity proofs.
- Docker tag `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` exists (Docker Hub, pushed
  2026-03-30) and matches the local switch — used by CI.
- Python oracle smoke-checked in-repo: `ω̄(C3)=2`, `ω̄(TT4)=1`
  (`uv run --with networkx python3 ...` against `scripts/core.py`).
