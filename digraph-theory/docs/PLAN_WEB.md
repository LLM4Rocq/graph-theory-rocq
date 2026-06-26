# Plan: the statement-audit website (and PDF) for digraph-theory

**Goal.** Make the library's results checkable by mathematicians with *no*
Rocq/MathComp background. The unit of consumption is **one result**: a
visitor interested in, say, "Conjecture 5.10 holds at k = 4" lands on a
page containing

1. the informal statement (paper-style, with the literature reference);
2. the **verbatim formal statement** (file + line, GitHub deep link);
3. a *Decoded* line — the Rocq text re-read as ordinary mathematics;
4. **the statement closure**: every definition and notation occurring in
   the statement, transitively, down to MathComp/graph-theory primitives —
   each with its informal meaning, its verbatim Rocq text, and a
   *faithfulness note* explaining why the formal object is the intended
   one (e.g. "ω̄ really minimises over **all** vertex orders: orders are
   `{perm T}`, and `ltp_realize` shows every strict total order is
   realized");
5. a *trust box*: axiom audit (`Print Assumptions` closed), what the
   kernel checks, what is deliberately **not** shown (proofs), and the
   independent oracle cross-checks;
6. a clickable dependency graph neighbourhood.

**Anti-goal.** No proofs, no proof-script exposition, no Rocq pedagogy
beyond what is needed to *read statements*.

**Precedent.** `../mathcomp-eulerian` ships both artifacts already:
`docs/formal/eulerian_formal.pdf` (Stanley-style PDF, auto-generated
catalog via `extract_catalog.py`) and `blueprint/` (rocqblueprint =
plasTeX site with `\uses{}` dependency graph, `\rocq{}` links, deployed
by `.github/workflows/blueprint.yml` to
`llm4rocq.github.io/mathcomp-eulerian`). We reuse that toolchain and CI
nearly verbatim; what is *new* here is the statement-closure machinery
(item 4) — the eulerian site is narrative-first, ours is result-first.

**Status:** v1.1 (2026-06-12) — **ALL MILESTONES M18–M21 COMPLETE**
(D16–D20 resolved with the recommended options). Exits: the closure
extractor + audit gate (33 results, 41 constants, 23 def-blocks,
8 tests), `docs/formal/digraph_formal.pdf` (47 pp), the blueprint site
(builds locally; deployed by `.github/workflows/blueprint.yml` with
coqdoc + PDF), CI gates: closure coverage, artifact freshness,
axiom audit (33/33 closed).

---

## 1. The catalog: what gets a page

Six result families (~26 result pages), each a blueprint chapter:

| Family | Results (each gets the 6-part template) |
|---|---|
| **U. The unified theorem** | `conjecture_5_10_at_345`; `conjecture_5_10_at_k3/k4/k5`; `question_5_9_fails_at_k3/k4/k5` |
| **A. k = 3: ACₙ** | `AC_kcritical3`, `omegabar_AC`, `omegabar_AC_del`, `card_AC`, `AC_vertex_transitive` |
| **B. k = 4: ACₙ[C₃]** | `T4_kcritical4`, `omegabar_T4`, `omegabar_T4_del`, `card_T4` |
| **C. k = 5: ACₙ[ACₙ]** | `T5_kcritical5`, `omegabar_T5`, `omegabar_T5_del`, `card_T5` |
| **P. Paths (Cheng–Keevash)** | `ck_conj1_delta3` (+ `_path` form), `ck_conj1_delta2`, `ck_theorem4_oriented`, `lemma7`, `no_short_strong3` |
| **G. General tournament theory** | `omegabar_lexprod_ge`, `vt_kcritical`, `omegabar_del_vt`, `domnum_le_omegabar`, `kcritical2_uniq` (C₃ unique 2-critical), `kcritical_proper_sub`, `omegabar_transb` |

Everything else (≈ 600 named results) appears only in an auto-generated
one-line catalog appendix (name, kind, docstring, GitHub link — the
eulerian Appendix-A treatment), clearly marked "internal machinery".

**The definition layer.** The statement closures of the 26 results hit a
modest, fixed vocabulary (estimate from the import structure):

- *Digraph-side (≈ 30):* `arc`/`-->`, `DiGraph`, `Oriented` (irrefl +
  asymm), `Tournament` (irrefl + total), `C3`, `TT`, `outdeg`, `ltp`,
  `backedge`, `omegab_at`, `omegabar`/`ω̄`, `kcritical`,
  `sub_tournament`, `del_tournament`, `lexprod`, `cayley`, `ACset`, `AC`,
  `dipath`, `ell`, `dicycle`, `strongb`, `dominatesb`/`domnum`, `autb`,
  `dgaut`, `vertex_transitiveb`, `transb`, `dgiso`.
- *External primitives (≈ 15, glossary entries):* `finType`, `#|T|`,
  `{set T}`, `{perm T}`, `'Z_n`, `val`, `==`/`is_true`, `[forall …]`,
  graph-theory's `sgraph`, `cliques`, `omega`.

Each Digraph definition gets **one** def-block (written once, reused by
every result page through `\uses` and the closure panel); externals get
glossary entries.

## 2. The faithfulness contract (what makes this auditable)

The site's promise to the reader: *"if you check the definitions on this
page, the kernel guarantees the theorem."* Three mechanisms back it:

1. **Closure completeness is machine-checked** (M18): a script computes,
   for each catalog result, the set of constants its *statement* (not
   proof) references, transitively through Digraph definitions; CI fails
   if any constant lacks a def-block on the corresponding page. No
   silently-missing definition — the failure mode that would make the
   whole site worthless.
2. **Verbatim Rocq text is extracted from source**, never hand-copied
   (the PDF/site re-build quotes the current `theories/` at build time;
   a stale quote is impossible).
3. **Axiom audit in CI**: the existing `Print Assumptions` checks become
   badges on the result pages.

Known faithfulness subtleties to write up explicitly (the things a
skeptical reader *should* ask):

- ω̄ minimises over `{perm T}` — why permutations exhaust all vertex
  orders (`ltp`, realization);
- `kcritical k T` uses boolean `forall` over vertices — finiteness makes
  this the literal mathematical statement;
- the backedge graph lives in coq-graph-theory's `sgraph`, and `omega`
  there is the genuine clique number (one glossary entry with *its*
  definition quoted);
- `'Z_n` arithmetic vs. integer residues (val arithmetic, n = 2m+1 ≥ 7
  encoded as `m'.+1.*2.+1` with `m' ≥ 2`: why the indexing is exactly
  "every odd n ≥ 7");
- "infinitely many" is rendered as `forall N, exists T, … N < #|T|`;
- `ell`/`dipath`: path length = number of arcs, simple = `uniq`.

## 3. Milestones

- **M18 — closure extraction + checker.**
  `scripts/statement_closure.py`: parse `_CoqProject`'s `.v` files,
  locate each catalog result's statement span (header → `Proof.`),
  harvest referenced constants from the build's `.glob` files within
  that span, close transitively through Digraph `Definition` bodies
  (stop at non-Digraph libraries), emit `docs/web/closure.json`.
  Plus `scripts/test_statement_closure.py` (sanity: e.g.
  `conjecture_5_10_at_345`'s closure contains `kcritical`, `omegabar`,
  `backedge`, `ltp`, `arc` and nothing proof-only).
  *Exit: closure.json for all 26 results, tests green.*
- **M19 — content: def-blocks and result pages, PDF first.**
  Write the LaTeX content (the slow, mathematical part) in
  blueprint-compatible macros, but build it first as a standalone PDF
  (`docs/formal/digraph_formal.pdf`, adapting the eulerian
  `docs/formal/` Makefile + `extract_catalog.py`): a 4-page
  "reading Rocq statements" primer, the six families as chapters with
  the 6-part template per result, the def-block library, the glossary,
  the auto-generated catalog appendix. The PDF is the reviewable draft
  of everything the site will show — and remains as the citable/offline
  artifact (per eulerian practice).
  *Exit: PDF builds in CI, content complete for all 26 results.*
- **M20 — the interactive site.**
  `blueprint/` à la eulerian: `rocqblueprint` + `plastexdepgraph`;
  chapters = the M19 content; every result block carries
  `\rocq{Digraph.<file>.<name>}` + `\rocqok` + `\uses{def:…}` (edges =
  the closure, *auto-emitted from closure.json* so the graph cannot
  drift); def-blocks collapsible; `.github/workflows/blueprint.yml`
  copied and adapted; deploy to GitHub Pages.
  *Exit: site live, dependency graph clickable, every result page
  self-contained.*
- **M21 — interactivity + QA hardening.**
  (a) The **closure panel**: on each result page an auto-generated
  "Everything this statement needs" box (from closure.json), ordered
  bottom-up, each entry linking to its def-block — this is the
  "more interactive than the PDF" deliverable.
  (b) CI coverage check (M18 checker wired in: missing def-block ⟹ red).
  (c) Verbatim-quote freshness check (quoted text ≡ current source).
  (d) Axiom-audit badges; GitHub deep links with line anchors.
  (e) README pointers; CHANGELOG; memory.
  *Exit: CI green on push including the three new checks; site URL in
  README.*

## 4. Decisions needing sign-off

- **D16 — site engine.** **Recommended: rocqblueprint** (as in
  mathcomp-eulerian): proven toolchain you already deploy, native
  dependency graph, PDF + web from one source, CI copyable. Fallbacks:
  bespoke static site from closure.json (maximum UX freedom, but we own
  every line of it), or coqdoc/Alectryon (statement extraction is poor
  fit — they are proof-display tools).
- **D17 — scope.** **Recommended: the 26-result catalog above** with the
  auto-generated appendix for the rest. Alternative: per-result pages
  for everything (×20 the def-block writing for machinery no
  mathematician will audit).
- **D18 — closure source of truth.** **Recommended: auto-extracted from
  `.glob` + CI completeness check**; the hand-written `\uses` edges are
  *generated*, not trusted. Fallback: manual `\uses` only (eulerian
  style) — simpler, but a missing definition becomes a silent content
  bug, which defeats the audit purpose.
- **D19 — deployment.** **Recommended: GitHub Pages of this repo**
  (`llm4rocq.github.io/digraph-theory`), blueprint workflow alongside
  the existing `ci.yml`.
- **D20 — PDF strategy.** **Recommended: PDF-first as M19** (your
  suggestion): the content is drafted and reviewed as
  `docs/formal/digraph_formal.pdf` (eulerian pipeline reused), then the
  same source feeds the blueprint. Alternative: blueprint-only with its
  `print.tex` target (one artifact fewer, but you lose the
  independently reviewable draft stage and the eulerian-style catalog
  PDF).

## 5. Risks

1. **plasTeX/listings vs. Unicode** (`ω̄`, `≤`, `'Z_n`, `⟹` in verbatim
   blocks): eulerian already solved the PDF side (`listings` config in
   `preamble.tex`); budget a day for the web renderer; fallback is
   ASCII-escaped quotes with the Unicode shown in the Decoded line.
2. **Statement-span extraction** edge cases (definitions by `:=`,
   section variables discharged into statements, notations like `ω̄(T)`
   hiding `omegabar`): the checker is exactly the tool that catches
   these; `.glob` references are notation-transparent.
3. **Section-discharged statements** read differently on the page than
   in the file (e.g. `omegabar_T4` quantifies over `m'` only after
   `End`): each result page quotes both the in-file statement and the
   full `About`-style discharged type, with one sentence on sections.
4. **Drift** between site and library on future milestones: the M21 CI
   checks make drift a red build, not a stale page.

## 6. What this buys

A mathematician can cite "Conjecture 5.10 holds for k ∈ {3,4,5},
machine-checked" after reading **one page** whose completeness is itself
machine-checked — and the same infrastructure documents every future
theorem the library acquires (the closure extractor and the template are
result-agnostic).
