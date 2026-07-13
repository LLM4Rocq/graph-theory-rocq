# Faithfulness audit — v2 statement waves X10–X110

> Independent review (2026-07-11) of the 101 conjecture-statement files authored in waves
> X10–X110 (115 `_statement : Prop` definitions across 12 area packages). Method: four
> area-partitioned faithfulness reviewers, then adversarial verification of every finding.
> **5 statements were refuted by a full machine-checked `~statement` proof (X35, X55, X83, X89,
> X100), 3 more by a machine-checked component-vacuity proof (X50, X90, X98), and the rest confirmed
> by definition/source analysis** — all axiom-free against the `digraph` switch. This document is the
> campaign record; it does not itself change any statement (fixes are tracked separately).

## Engineering pass — clean

- **101 files / 115 statements**, all compile axiom-free under Rocq 9.1.1 (fresh `.vo`; an
  8-statement cross-area `Print Assumptions` sample and every machine-checked proof below report
  *Closed under the global context*).
- No `Admitted` / `Axiom` / `Parameter` / `admit` / `:= True|False` placeholder anywhere. The 14
  files carrying `Qed` proofs only discharge `symmetric` / `irreflexive` obligations to *construct*
  graphs (line graph, complement, add-edge, diamond, claw, path) — none proves a `_statement`.
- Every file is registered in its `_CoqProject`, statement names are unique, and all 115 are
  tracked in `v2_statement_waves.json` with a recorded source-readback pass.

## Faithfulness pass — 15 confirmed encoding defects / 115 (≈13%)

Four area-partitioned reviewers flagged 20 statements; adversarial verification confirmed **15
genuine encoding defects**, **overturned 2** as faithful-after-all on deeper source reading (X16, X36 —
see "Not defects"), and cleared the rest. Every confirmed defect **passed the campaign's own
source-readback pass** — the readback did not catch over-permissive hypotheses or vacuity. See "Root
cause" for the systemic fix, and "Resolution" for what was applied.

### Tier 1 — machine-checked (provably vacuous or refutable in Coq; not disputable)

| ID | Area | Sev | Machine-checked defect | Fix |
|----|------|-----|------------------------|-----|
| X100 | chromatic | HIGH | `~statement` compiles. `x100_modular_weight`/adjacent-distinct-mod-k is **not** χ′ₖ: K₄ at k=2 forces 4 pairwise-distinct weights mod 2 → injective `K₄ → 'I_2` → `4 ≤ 2`. | Re-encode χ′ₖ (Botler–Colucci–Kohayakawa colour-class degree condition). |
| X35 | chromatic | HIGH | `~statement` compiles. `x35_nontrivial_cut X` = "nonempty proper subset", **not a separator**: at k=1 hyps hold on the edgeless graph E₂ but `χ(induced X) < 1` is impossible for nonempty X; at k≥2 a single vertex trivially witnesses (sparsity premise inert). | Make `x35_nontrivial_cut` a genuine separator; exclude k=1 / single-vertex cuts. |
| X83 | chromatic | HIGH | `~statement` compiles. `col : G → C` has no properness guard: on K₂ (triangle-free, χ=2) a constant colouring makes `uniq (map col p)` false for the size-2 path → no rainbow induced path of size χ. | Add `x3_proper_colouring col ->`. |
| X89 | misc | HIGH | `~statement` compiles. `x89_quartet_shape` is a **free record field** decoupled from topology: two trees on the same graph with constant shapes 0 and 1 differ on all `'C(n,4)` quartets ⇒ max distance = `'C(n,4)` ⇒ f(n)=`'C(n,4)`, contradicting the ⅔-asymptotic at q=4 (`12·C ≤ 11·C`). | Make shape a *defined function* of graph+leaves, not free data. |
| X90 | digraph | HIGH | Triviality compiles: `x90_in_np P` proven **always True** (`cert_size := 0`). cost/cert/red are decoupled from any computation ⇒ the NP/reduction classes are vacuous. | Tie cost/cert/reduction to a verifier/decider bounded by the polynomial. |
| X98 | extremal | MED | Triviality compiles: `x98_induced_subdivision` forces neither internally-disjoint paths nor global inducedness ⇒ strictly weaker than a real induced subdivision. | Require pairwise-internally-disjoint paths + global non-adjacency of the union. |
| X55 | misc | MED | `~statement` compiles. Missing `n ≥ 2` guard: the 1-point metric space has no `a ≠ b`, so 0 lines and no universal line ⇒ `1 ≤ 0`. (Sibling X110 has the guard.) | Add `2 <= #\|V\|`. |

*Partial:* **X50** (chromatic, MED) — hypothesis-collapse machine-checked: `has_girth` is *exact* girth and is empty on any acyclic graph, so a triangle-free **forest** F (e.g. K₂) forces `x50_same_girth F G` to make G acyclic ⇒ χ(G) ≤ 2, contradicting `target ≤ χ(G)`. Only the textbook "acyclic ⇒ χ ≤ 2" step is left un-compiled. Fix: require F to contain a cycle (`exists g, has_girth F g`).

### Tier 2 — confirmed by definition/source analysis (verify against the primary source before fixing)

| ID | Area | Sev | Defect | Fix |
|----|------|-----|--------|-----|
| X88 | extremal | HIGH | Dominates `x88_clique_count` (#Kᵣ) instead of BCLLP's `Dᵣ` (edges to delete to make r-partite); the Turán graph maximizes both e(G) and #Kᵣ (Zykov) ⇒ `G* := T(n,r)` dominates every instance ⇒ vacuous. | Replace with a `Dᵣ` primitive. |
| X41 | misc | HIGH | Requires **both** pure-pair sides linear; the Conlon–Fox–Sudakov "sparse linear" conjecture is asymmetric (polynomial × linear). Both-linear is false (pseudorandom triangle-free graphs). | One side `≥ εn^ε`. |
| X58 | extremal | HIGH | Two **linear** anticomplete sets ∀H; CFSSS (arXiv:1810.00058) asks polynomial × linear (linear × linear only for forests). | Weaken side A to polynomial; two-linear only for forest H. |
| X54 | digraph | MED | `x54_no_induced_odd_dicycle` quantifies over all S ⇒ collapses to "no odd dicycle at all"; the conjecture (Q3.2) excludes only *chordless* odd dicycles. | Forbid only chordless odd dicycles. |
| X45 | digraph | MED | Existential `β < 1` instead of majority `β = 1/2` (as sibling X51) ⇒ strict weakening. | Fix threshold `2·same ≤ outdeg`. |
| X34 | chromatic | MED | Guard `7 ≤ Δ`; source (arXiv:2302.13312) states odd `Δ ≥ 9` ⇒ too strong. | `9 ≤ Δ`. |
| X102 | misc | MED | `x102_subdivided_multiclaw` only caps degree>2 vertices at 1/component but allows arbitrarily many leaves; the forbidden family should be tripods (≤3 legs). | Cap leaves/branch-degree at 3. |

## Not defects

- **X16** (digraph) — **overturned on deeper source reading.** The audit initially flagged that
  `spiro_quasi_kernel_half_covered_statement` drops `x16_no_sources`. But Spiro's *Large* Quasikernel
  Conjecture (arXiv:2404.07305, Conj. 2.6) is stated for **every** digraph (`|N⁺[Q]| ≥ |V|/2`); the
  source-free hypothesis belongs to the *Small* Quasikernel Conjecture, encoded by the sibling row.
  The current statement is faithful — adding `no_sources` would *weaken* it. **No change.**
- **X36** (extremal) — **overturned.** The Alon–Friedland–Kalai conjecture (arXiv:2507.04254, Conj. 4)
  states `e(G) ≤ (k−1)n` with a **non-strict** bound and `k ≥ 1`; the current `≤` encoding is faithful.
  Making it strict would be *unfaithful*. **No change.**
- **X85** (extremal, LOW) — **false positive.** The existentially-quantified exponential base is a
  faithful, defensible weakening. No change.
- **X14** (misc), **X92**, **X73** (digraph) — **faithful encodings of since-*disproven* conjectures**
  (BDDFK / Haxell–Scott arXiv:1406.7227; the inversion-number and ACH d-regular bounds). Not encoding
  bugs — a *curation* question (whether refuted conjectures belong in the "done" set). Annotate.

## Resolution (applied 2026-07-11, working-tree edits)

Each fix was designed against the primary source, scratch-verified to compile axiom-free, and confirmed
to remove the defect (the old refutation/triviality no longer type-checks); then re-applied in place with
a compile + no-rename + axiom-free gate. Fixes touch only statement/vocabulary bodies (names unchanged,
so manifest tracking is intact).

- **Applied (14):** X34, X35, X41, X45, X50, X54, X55, X58, X83, X88, X89, X98, X100, X102. Mechanical
  (guard/threshold/mirror-sibling): X34 (`9≤Δ`), X45 (majority β=½ per X51), X50 (F must contain a
  cycle), X55 (`2≤#|V|`), X83 (proper colouring). Substantive re-formalization (review recommended):
  X35 (real `disconnected` separator), X41/X58 (asymmetric polynomial×linear pure pair), X54 (chordless
  odd dicycle), X88 (`D_r` edit-distance in place of clique count), X98 (genuine induced-subdivision
  model: injective branch map, internally-disjoint paths, global inducedness), X100 (modular χ′ₖ:
  each colour's nonzero vertex-degrees ≡ 1 mod k), X102 (subcubic ⇒ tripod family), **X89** (quartet
  shape becomes a DEFINED edge-separation function on a *trivalent* tree, replacing the free record
  field — applied on author sign-off).
- **Reclassified `blocked` (1):** **X90** — no faithful fix without a genuine poly-TIME computation
  model (absent from mathcomp/GTBase); a bare decider has no runtime to bound, so the dichotomy stays
  vacuous. Now tracked as `blocked` — "needs a layer deliberately out of scope" (v2 statement legs:
  277 done / **1 blocked**). Wiring: `state: "blocked"` + `blocked_reason` on the X90 row in
  `v2_statement_waves.json` (the generator honors a per-wave-row `state`), so it keeps its
  formal_name/phase and the milestone gate still checks `X90.v` compiles axiom-free. Design options
  for a real fix are in `meta/X90_polytime_fix_sketch.md`; also flagged in-source with a
  `FAITHFULNESS DEFECT` comment.

After the fixes, `vacuity_probe.py` reports all five statements with witness hints
(X35, X55, X83, X89, X100) as `stale-FIX-OK` — their refutations no longer compile against the
corrected statements.

## Root cause & the missing gate check

All defects are one failure mode: **over-permissive hypotheses/definitions** — an arbitrary function
where a *proper* one is meant (X83), a "cut" that isn't a separator (X35), a free record field (X89),
decoupled cost functions (X90), a symmetric bound where the source is asymmetric (X41/X58), a wrong
dominated quantity (X88). Six are *internally* vacuous or refutable, so a cheap automated probe catches
them without knowing the source.

`check_milestone.py` step 7 already *rejects committed* trivial proofs/refutations, and
`faithfulness_mutation.py` mutation-tests the checks — but neither *actively searches* for a trivial
proof of each statement. The gap is an **active vacuity/refutability probe** (`meta/vacuity_probe.py`,
`make probe`) with two layers, for each `_statement` trying to close both `statement` and `~ statement`:

- **auto tripwire** — a bounded ssreflect/`eauto`/`firstorder` ladder. High precision, but on this
  batch its recall is **0/5**: the Tier-1 refutations need a bespoke finite counterexample (a K₄
  pigeonhole, a constant colouring of K₂, two star-trees) that generic automation does not find. Its
  real value is forward: it catches any *globally* trivially-true/false statement authored in future.
- **witness hints** (`meta/probe_hints/<name>.v`) — the curated machine-checked counterexamples from
  this audit. Recall **5/5**, false positives **0/6** (validated: `vacuity_probe.py --validate`). These
  also serve as fix-verification: once a statement is corrected, its witness must stop compiling
  (`hint: stale-FIX-OK`).

Honest takeaway: automation alone would *not* have caught these — a human/agent still had to find each
counterexample. But once found, the probe makes them permanent regression guards, and the auto layer is
a cheap standing net against the trivially-vacuous case. The higher-recall future direction is a
finite-model instantiation harness (specialize `forall (G:sgraph)…` over a small concrete-graph catalog
and `vm_compute` the decidable body), sketched but not yet built.

## Reproducing the machine-checked refutations

The seven Tier-1 proofs compile against the `digraph` opam switch (Rocq 9.1.1), e.g. for X100:

```
coqc -q -Q base/theories GTBase -Q chromatic-theory/theories Chromatic -w -notation-overridden <file>
```

with body:

```coq
Lemma X100_refuted : ~ modular_edge_colouring_k_plus_constant_statement.
Proof.
rewrite /modular_edge_colouring_k_plus_constant_statement => H.
have [C /(_ (complete 4)) [col Hcol]] := H 2 (leqnn 2).
pose g (v : complete 4) : 'I_2 := Ordinal (ltn_pmod (x100_modular_weight col v) (ltn0Sn 1)).
have ginj : injective g.
  move=> x y /(congr1 (@nat_of_ord 2)) /= exy.
  case: (eqVneq x y) => // xney.
  by move: (Hcol x y xney); rewrite exy eqxx.
have := leq_card g ginj. by rewrite !card_ord.
Qed.
```
