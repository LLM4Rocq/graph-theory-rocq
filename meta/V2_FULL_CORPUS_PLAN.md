# v2 — Formalize every conjecture in `graph-conjectures`

**Status: PLAN (rev 3, 2026-07-07).** Successor programme to
[`OPG_FULL_FORMALIZATION_PLAN.md`](OPG_FULL_FORMALIZATION_PLAN.md) (v1, complete:
227/227 OPG rows attempted, statement-complete, release `opg-v1.0.1-227-attempted`).
Rev 2 incorporated a three-critic adversarial audit of rev 1: all counts below were
recomputed from the primary JSON/MD sources on 2026-07-07; heuristic-sensitive counts
are given as bands and get pinned exactly in X0b. Rev 3 tightens seven contracts per
maintainer review: S6 scope (every cluster now tracked), T2-bound refuted derived
rows kept as `disproved`, auditable source verification (tuple, not boolean), the X0
split into X0a–X0d, normalized (not verbatim) source storage, canonical cross-corpus
node identity, and T-track resequencing/resizing.

**Goal.** Every conjecture recorded anywhere in
`/Users/lelarge/Recherche/graph-conjectures` gets a tracked manifest row in this
repo, and every row that is formalizable under our standing foundations gets an
axiom-free `Definition <name>_statement : Prop` passing the full v1 gate + faithfulness
stack. On top of the statements, a theorem/certificate track formalizes the *proved*
results and *refutation certificates* accumulated by the attack engine in
`graph-conjectures/problems/`.

---

## 0. Source inventory (verified + adversarially re-audited 2026-07-07)

`graph-conjectures` contains **six** conjecture-bearing sources. Slug-level comparison
against `meta/opg_corpus_manifest.json` established:

| # | Source | Size | Overlap with v1 (OPG 227) | Disposition |
|---|--------|------|---------------------------|-------------|
| S1 | `data/problems.json` (OPG scrape) | 227 problems | **identical** (227/227 slugs) | DONE in v1 — no new work |
| S2 | `data/arxiv_conjectures.json` (arXiv mining, 425 papers, 2016–2026) | **762 records** | 40 records (5.2%) from the 23 accepted-match papers present in the corpus (`data/arxiv_opg_matches.json`: 44 papers manual_confirmed of 142 candidates, 98 rejected → 21 distinct OPG problems) | **The main v2 corpus** |
| S3 | `ABOULKER_CONJECTURES_RANKED.md` | 56 records / 19 papers | strict **subset of S2** (the Aboulker-coauthored slice); its errata block has 5 entries of which **3 are status corrections** not yet reflected in S2's review files | Merge as curation metadata onto S2 rows |
| S4 | `problems/` attack folders | **19 folders** (2 twins → 18 distinct problems) | 6 folders = OPG rows already formalized in v1; 11 newer folders = S2 rows (Aboulker papers); 1 (directed_path/Cheng–Keevash) in S2 | Statements via S2/v1 rows + **engine-derived rows** (§1 B6) + the **theorem/certificate track** (§5) |
| S5 | `data/erdos_graph.json` (erdosproblems.com scrape, credited to Thomas Bloom) | **277 records** (143 open, 134 solved), each with full LaTeX statement, tags, citations | `data/intersection.json` maps **15** to OPG slugs; ≥262 have no v1 row | **Second v2 corpus** (decision D6, default in-scope) |
| S6 | `data/arxiv_extracted/` "studies"-role slice | 1,565 raw records = 819 `states` (→ the 762 curated) + **746 `studies`**; ~669 distinct titled third-party conjectures with statement_text, **~618 title-match neither S1 nor S2** (Steinberg, LECC, Hajós k=5, Tomescu, …) | small (title-normalization) | Adjudicated in **X0d**: every deduped cluster gets a tracked row; D7 governs only the statement-promotion bar |

Supporting facts about S2 (recomputed from the JSON):

- **Kinds:** 262 Conjecture, 174 Problem, 140 Question, 186 Informal. Extraction
  confidence: 419 high / 314 medium / 29 low.
- **Review status** (live `data/arxiv_reviews/` counts; the ranking MD of 2026-05-16 is
  one record stale): **685 open+partial** (553 open, 132 partial); **77 resolved/other**
  (58 solved, 14 disproved, 5 unclear). Difficulty tiers ≈ 22/131/359/165/8 — recorded
  as metadata, not a scheduling driver.
- **Topic split** (keyword heuristic — sensitive to which text fields are scanned):
  ~86% graph/digraph/hypergraph; directed **109–121**, hypergraph **19–35**,
  non-graph combinatorics **77–120** (additive/NT, algebra, discrete geometry, misc).
  Exact buckets pinned by the X0b classifier run.
- **Statement quality:** a 30-record manual sample says ~40% crisp / ~43%
  precise-but-paper-local-notation / ~17% vague (sample-derived estimates; the
  per-record truth comes from X0b triage). Records needing *source recovery* before
  formalization — the union (not sum; the buckets overlap) of too-short (<59 chars,
  57), internal-reference ("Theorem 1", 50–64 depending on regex), and missing (1) —
  is **≈105–120**. X0b pins the exact regex/threshold definitions so the number is
  reproducible.
- Raw material for recovery exists: `data/arxiv_extracted/` (857 per-paper files) and
  the upstream scraper pipeline.

**Bottom line.** v2 = onboard S2 (762 rows; a realistic ~440–580 become faithful
statements, the rest parked with documented reasons) + S5 (277 rows, 15 of them
aliases), fold in S3 as curation, mine S4 for derived rows and its proved-theorem
layer, and track every S6 cluster. Order of magnitude: **~1,700+ tracked rows
repo-wide** (227 v1 frozen + 762 S2 + 277 S5 + ~669 S6 clusters + derived), of which
roughly **600–850 statement targets**.

---

## 1. Corpus definition — from records to manifest rows

Every S2/S5 record and every S6 cluster gets a manifest row; nothing is silently
dropped (v1 invariant: attempted = total, every non-done row carries a note).

### 1.1 S2 triage buckets

- **B1 — alias-of-OPG (≤40).** The 40 records from the 23 accepted-match papers
  present in the corpus. Per-record adjudication: true restatement →
  `alias_of: <opg_slug>` row (no new statement); variant/strengthening → normal row +
  `@EDGE` to the OPG row. The match is per-paper, so 40 is an upper bound; expect
  ~20–30 true aliases.
- **B2 — direct statement targets.** Kind ∈ {Conjecture, Problem, Question}, statement
  self-contained modulo standard vocabulary. Expected ~400–450 after B1/B4/B5
  removals. *Resolved* records (77: 58 solved, 14 disproved, 5 unclear) still get
  statements — they feed faithfulness technique #2 (right-polarity proofs), exactly
  like v1's solved/disproved rows.
- **B3 — statement-recovery targets (≈105–120).** Precise mathematics but the record
  alone is insufficient (internal refs, truncation, paper-local notation). New
  pipeline stage **REC** (§3) recovers the exact statement from the arXiv TeX; then
  they join B2. Recovery-failed → park with reason.
- **B4 — vague/meta (park).** "It would be interesting…", value-determination without
  a candidate bound, "characterize…" without a conjectured answer — concentrated in
  (but not coextensive with) the 186 Informal records; per-record triage in X0b
  decides. Park as `unformalizable-as-stated` with note; where the paper or engine
  names a concrete finite handle (e.g. m(k) bounds for chordal digraphs), add a
  *derived* row (B6) instead.
- **B5 — out-of-scope-for-now (77–120).** Non-graph combinatorics. Rows exist with
  `defer_reason: out-of-scope-v2`; see decision D1. Note: F_p^n additive combinatorics
  is stateable **today** (mathcomp `all_algebra`: `'F_p`, `'rV[_]_n` — verified against
  the installed switch); general F_q needs the `rocq-mathcomp-field` opam dep — an
  add, not a re-architecture.
- **B6 — engine-derived rows (count pinned at X0c, not guessed).** The attack engine's
  actual working targets, absent from S2 as records. Enumeration rule: parse
  `live_hypotheses` from every `ledger.json` (10 folders have one; **82 entries**
  observed, e.g. tournament_clique 19, chen_chvatal 11, twinwidth 11, arc_disjoint 8),
  **plus refuted entries whose counterexample the T2 track plans to certify** — those
  become rows with `status: disproved`, so the exact-type gate expects the
  `~ <name>_statement` polarity and T2 has a row to anchor to (per the ownership rule
  in §1.4, the row is created here; T2 only appends proofs). Drop only
  RETIRED/superseded entries with no formalization payoff, each with a one-line
  reason. **And** doc-mine the **9 ledgerless folders**
  (3_decomposition, crossing_numbers, directed_path, earth_moon, path_matching_fas,
  pebbling, positive_square_energy, unit_vector_flows, unvd — their targets live only
  in `docs/*.md`/README/PROBLEMS_OVERVIEW, e.g. 3-decomposition's Lemma C /
  cycle-bypass / M-axis dichotomy, WC3, Universal Replacement Conjecture,
  L-exist/L-swap, H1, Conjecture 6.2 + HALF A/B, H5/Lemma A/C2, χ_EM sub-brackets).
  Selection criterion for a row: a *single proposition* with a finite/oracle handle.
  Tracked with `corpus: derived` and `parent` pointers; ledgers are living documents,
  so every derived row snapshots its ledger commit/date.

### 1.2 S5 (erdosproblems) triage

15 rows alias onto v1 OPG rows per `data/intersection.json`; the remaining ~262 get
rows with `corpus: erdos` (+ erdős number, URL, prize, citation keys). 143 open feed
statement waves; 134 solved feed technique #2 polarity work. Same formalizability
classifier as S2; expect a similar park rate for asymptotics-heavy entries. Statements
in `erdos_graph.json` are curated LaTeX (closer to OPG quality than S2), so most rows
skip REC.

### 1.3 S6 (studies-role) adjudication — every cluster tracked

Dedupe the ~669 titles into clusters; **every cluster gets a manifest row**
(`corpus: arxiv-studied`), so the headline goal — every conjecture recorded anywhere
gets a tracked row — holds without exception. Each row carries a `disposition`:
(a) `alias` of an existing S1/S2/S5 row; (b) `edge-anchor` — "paper P studies
conjecture C, proving partial result R" is exactly the atlas material of §6, and the
row gives that edge a canonical endpoint; (c) `promoted` — genuinely new named
conjecture with self-contained statement, enters the statement waves;
(d) `parked` (`studies-backlog`, with note). Default posture (D7): promote *named,
third-party-attributed* conjectures only; anonymous paper-local fragments stay
tracked but parked. Alias/edge-anchor/parked rows count as attempted for the
statement-complete target; only `promoted` rows owe a statement.

### 1.4 Manifest

New file `meta/v2_corpus_manifest.json` (file-level `schema_version`), same row
schema as v1 plus:

- **Identity:** `row_id` — canonical, corpus-qualified, stable
  (`arxiv:2310.04265#c3.12`, `erdos:19`, `derived:tournament_clique/H16`,
  `studies:steinberg`). An `alias_of` row is never an edge endpoint or a statement
  owner; all tooling normalizes references to the canonical `row_id` (§6).
- **Provenance:** `corpus ∈ {arxiv, erdos, derived, arxiv-studied}`,
  `arxiv_id`/`erdos_id`, `record_key`, `kind`, `parent`, `disposition` (S6 rows),
  `alias_of`.
- **Status:** `review_status` (raw) + `review_date`, `difficulty_tier`,
  `status_verified_at`.
- **Recovery & verification (auditable, not boolean):**
  `recovery ∈ {none, needed, done, failed}`, `source_locator` (arXiv id + version +
  statement number / erdős URL), `source_hash` (checksum of the consulted source
  fragment), `source_excerpt` (short, license-permitting — §2), `implemented_by`,
  `source_verified_by`, `source_verified_at`, `verification_note`. The convenience
  flag `source_verified` is *derived*: true iff locator+hash present ∧
  `source_verified_by` non-empty ∧ `source_verified_by ≠ implemented_by`. The gate
  checks the tuple, never the flag.
- **Legal:** `license` (§2).

**Status-field rule (gate compatibility).** `meta/check_milestone.py` hardcodes the v1
vocabulary read from `row["status"]` (refutation forbidden unless `disproved`, direct
proof forbidden when `open`/`partial`). The X0b builder therefore **populates `status`
from the review vocabulary by identity mapping** (open/partial/solved/disproved) and
maps **`unclear` → `open`** (safest: forbids committed direct proofs; the 5 unclear
records get an SVER pass). A v2 mutation canary on a review-`disproved` row proves the
mapping end-to-end.

**Status precedence (single source of truth).** When sources disagree:
paper-review file < S3 errata < SVER citation check < engine-ledger proved/refuted
item that passed the ledger's red-team gate. Every T-track milestone re-snapshots its
folder's ledger at milestone start (the B6/T1 lists in this plan are a 2026-07-07
snapshot — e.g. tournament_clique's P22/P23 already postdate rev 1).

**Row ownership.** Statement waves own manifest rows; the T-track appends legs/
artifacts to existing rows, never creates competing ones.

### 1.5 Reconciliation head start (X1)

`digraph-theory/docs/digraph_conjecture_ledger.json` +
`digraph_conjecture_classification.json` map 148 directed records (37 OPG + 111
arXiv; **106 unique** after `duplicate_of` folding) onto S2 **byte-identically on
(arxiv_id, title)** — spot-checked 5/5. `digraph-theory/theories/conjectures/` already
contains ~67 non-P9 Prop constants, of which **~35–40 are genuine conjecture
statements** for S2 rows (in `heroes_dichotomy.v`, `two_extremal*.v`, `twinwidth*.v`,
`unvd.v`, `path_fas.v`, `sad.v`, `chi_bounded.v`, …; `dichromatic.v` is definitional).
X1 closes these at **low** (not zero) marginal cost: per-row source-verification is
still required, several constants don't follow the `<formal_name>_statement`
convention (`conj_9`, `conjecture_P`, …), and each row needs manifest+overlay entries
plus a gate run. Note: some constants there are engine-derived targets (WC3, CL1,
`pathFAS_iff_LFO`) → they reconcile against B6 rows, and `bang_jensen_yeo_SAD`
predates 2016 so it has no S2 record (it's an OPG row).

---

## 2. Deliverables & invariants (unchanged from v1 unless stated)

Per formalizable row, the five legs: **statement** (axiom-free
`Definition <formal_name> : Prop`, Print Assumptions clean, exact-type gate),
**grounding** (`grounding_<phase>.v` Qed witnesses: inhabitation, guard-has-teeth,
primitive content, structural laws), **edges** (`implications_<phase>.v` with `@EDGE`
annotations; Qed only for verified-literature edges), **correspondence** (readback
entry), **audit_page**. Status semantics done/partial/blocked identical to v1; overlay
`meta/v2_legs_state.json` with commit+package provenance and notes.

Standing invariants: axiom-free throughout; area packages import only `GTBase` (plus
the two sanctioned topological exceptions); local-first vocabulary with `BASE-MOVE`
promotion at ≥2 areas; `make audit` toolchain-free in CI; `make gate` full acceptance;
mutation suite grows with every new load-bearing definition.

**New invariant (v2): source-verification (auditable).** v1's `source_text` was
canonical OPG prose. S2's `statement_text` is an LLM extraction — so a row may only
reach `statement: done` when its verification *tuple* is complete (§1.4):
`source_locator` + `source_hash` present, `source_verified_by` recorded and
**distinct from** `implemented_by`, `source_verified_at` stamped, with the check made
against the paper's TeX (not just the JSON record). A bare boolean is not auditable;
the tuple is. This is **net-new gate code** (a `check_milestone.py` step-6 extension),
not configuration. Known failure modes it catches: truncated itemized conclusions
(2310.04265 Conj 3.13/3.16), conflicting author attribution (arXiv:1606.06011 — the
two Chen–Chvátal folders disagree), stale review statuses (3 S3 errata flips; Aubian
2024 refuted 2310.04265 Conj 4.3 *after* the review sweep; 2410.16495 Q1.1 flipped to
disproved after the ranking MD was generated).

**New invariant (v2): licensing/attribution — store normalized, not verbatim.** The
repo is Apache-2.0 but embeds third-party statement text: OPG prose (GFDL v1.2 per
upstream `LICENSE-DATA.md` — this already applies to the v1 manifest) and
erdosproblems.com content (attribution: Thomas Bloom). For arXiv material the safe
design is: the manifest carries **our own normalized statement** plus
`source_locator` + `source_hash` + `license` metadata; verbatim text lives only in
short `source_excerpt`s where the paper's license permits (CC-BY → full quote fine;
arXiv default license → excerpt-minimal or none). X0a deliverable: a
`LICENSE-DATA.md`-style dual notice + the per-row `license` field, settled **before**
any v2 source/excerpt fields are populated.

---

## 3. Pipeline changes vs v1 (with honest costs)

Milestone assignment: items 1–3, 6, and 8 land in **X0a** (schema / routing / gates /
licensing — before any v2 row exists); item 7 runs in **X0b**; items 4–5 are standing
stages exercised from X0b onward.

1. **Multi-corpus status tooling — a rewrite, not a tweak (~1 day).**
   `meta/report_corpus_status.py` is single-corpus throughout (hardcoded paths, NS
   map, `total == 227` assert at line 153, v1 prose in the report body) and its
   invariants "0 todo / done+partial+blocked == total" describe v1's *final* state.
   v2 needs per-corpus sections with per-corpus invariants: OPG frozen (227, 0 todo);
   v2 growing (overlay-consistency only; todo allowed until statement-complete).
   First action: fix the stale README counts (says 212/8/7; the gate's authority is
   **208/12/7** since the D3cr downgrade) and make the generated report the single
   source of truth. `build_opg_manifest.py`'s own 227-assert stays (OPG-only tool).
2. **Edge-graph cross-corpus fix + node identity.** `meta/build_edge_graph.py`
   filters digraph-hosted edges to OPG `corpus_nodes` only (line 75) and drops
   non-OPG endpoints *silently* — X1/X2 `@EDGE`s would vanish. X0a: union
   `corpus_nodes` over all manifests, loud warning on filtered edges, **and endpoint
   normalization rules**: every endpoint resolves to a canonical `row_id` (§1.4)
   before the graph is built or checked; an edge written against an `alias_of` row is
   rewritten to its canonical target (recorded in `sources`) or rejected;
   `formal_name` stays the Rocq-level key, but the graph is keyed by `row_id` so
   S2/S5 duplicates and aliases cannot produce ambiguous or doubled edges.
3. **Corpus-routing module (~2–3 days incl. tests).** The manifest path lives in
   `milestone_rows.py` (not `check_milestone.py`), the overlay path is hardcoded, and
   the NS map is **triplicated** (check_milestone / report_corpus_status / workflow
   template). X0a factors a shared routing module (phase → manifest + overlay + NS),
   imported by all four scripts, and adds: the `source_verified` gate check, and a
   **reconciliation mode** — `make_milestone_workflow.py` currently *refuses*
   milestones whose rows are all `already_formalized`, which is exactly X1.
4. **New stage REC (statement recovery).** For B3 rows: a dedicated recovery worker
   fetches/parses the paper TeX (scraper + `data/arxiv_extracted/`; fresh fetch when
   the extract is insufficient), reconstructs the exact statement + local definitions
   into the manifest row (`recovery: done`; normalized statement + locator/hash/
   license per §2, short excerpts only where licensing permits), with a mandatory
   second-reader check completing the verification tuple (§1.4), and an explicit
   `recovery: failed → park` exit. Throughput planning: ~15 rows per REC
   sub-milestone, interleaved with waves (X7 rolling).
5. **New stage SVER (status re-verification) — with a cadence, not just a trigger.**
   Before a wave lands: re-verify `review_status` for its rows (tier-4/5 rows and all
   rows whose technique-#2 polarity or exact-type gate depends on status get a
   citation check; record `status_verified_date`). After landing: a **periodic
   re-sweep** (quarterly, and at every release) over all landed done/partial rows; a
   post-landing flip updates `status`/`status_semantics`, re-checks technique-#2
   polarity, and never deletes a statement.
6. **Milestone machinery.** Revive `meta/area_milestone_pipeline.workflow.js`
   (archived with two documented restart corrections) with REC/SVER stages in front —
   after verifying the external Workflow harness is still available (fallback: drive
   milestones manually as the P9/D-waves were). Parameterize `make_milestone_workflow.py`'s
   hardcoded MANIFEST/PLAN references by corpus; the 434-line template needs a real
   editing pass (v1-specific prose: G2 planarity gates, OPG source_text audit).
7. **Classifier.** Re-run the v1 formalizability classifier over S2+S5; add
   `needs-source-recovery` and `out-of-scope-v2` buckets. Difficulty tier is recorded
   but does NOT drive scheduling — statement difficulty ≠ proof difficulty (tier-5
   χ-boundedness statements are among the easiest to state).
8. **Mutation suite.** Mutants are plain entries in `faithfulness_mutation.py`'s
   MUTANTS list — extension is easy, but (a) sequence v2 mutants *after* the routing
   change (the runner shells `check_milestone.py <phase> <pkg>`), (b) extend
   `copy_workspace` to include sibling deps parsed from `_CoqProject` before targeting
   hamiltonicity/packing (their topological dep isn't copied today), (c) add the
   review-disproved status-mapping canary (§1.4).
9. **CI scaling.** The OPG-227 gate remains a required blocking check for every v2
   commit. Measure `make gate` wall-time at X1/X3 boundaries; shard per corpus/package
   if it outgrows the budget (~1,050+ rows and the T-track's proof files are coming).

---

## 4. Statement waves (phase codes X*, XE*; no collision with U*/P*/D* — verified)

Batch sizing follows v1 experience (~15–40 rows per milestone, sub-batched by
vocabulary). Ordering maximizes reuse: directed first (mature package + X1 head
start), then the big undirected chromatic/structural mass, then specialty areas, then
recovery-gated and parked tails.

| Phase | Content | Est. rows | Packages | New primitives (expected) |
|-------|---------|-----------|----------|---------------------------|
| **X0a** | Schema / routing / gates / licensing: §3 items 1–3, 6, 8; manifest `schema_version` + `row_id` scheme; licensing notice; README count fix. **No v2 rows generated yet.** | — | meta | — |
| **X0b** | S2+S5 manifest build: all 1,039 rows created; B1/S5-alias adjudication; S3 errata merge; classifier run; bucket regexes committed → **every count in this plan pinned** | 1,039 rows | meta | — |
| **X0c** | B6 enumeration: ledger parsing (incl. T2-bound refuted targets as `disproved` rows) + doc-mining the 9 ledgerless folders | pinned here | meta | — |
| **X0d** | S6 adjudication: ~669 clusters deduped, one tracked row each with `disposition` | ~669 rows | meta | — |
| **X1** | Directed reconciliation: map the ~35–40 existing digraph-theory constants onto S2/B6 rows; re-audit under v2 gates | ~60–80 rows touched | digraph | few (ω⃗ backedge, unvd, twin-width partially exist) |
| **X2** | Directed new statements (rest of the 109–121 directed records + directed B6 rows) | ~40–60 | digraph | mader_δ⁺/δ⁰, blow-up/extension ops, unavoidability variants |
| **X3** | χ-boundedness / coloring / Gyárfás–Sumner ecosystem (largest cluster, incl. the tier-5 head) | ~80–100 | chromatic, homomorphism | poly-χ-boundedness, ordered graphs, holes-of-consecutive-lengths |
| **X4** | Extremal / Ramsey / density / probabilistic-flavored | ~60–80 | extremal | rcfType asymptotic idioms (v1 D2 pattern) |
| **X5** | Structural: minors, treewidth/sparsity, matchings, packing, cycles, hamiltonicity | ~60–80 | minor, packing, cycle, hamiltonicity, misc | merge-width, product structure |
| **X6** | Hypergraphs (19–35) + spectral (s± energy) + topological (crossing, thickness/biplanarity) | ~40–50 | hypergraph, spectral, topological | s± (extends `spectral.v`), biplanarity (pair of `wagner_planar` layers), pebbling |
| **XE1–XE2** | S5 erdosproblems corpus: 143 open + 134 solved (polarity targets), minus 15 aliases and parked rows | ~150–250 | per-topic (same areas) | mostly covered by existing vocabulary |
| **X7** | Recovery-gated tail: B3 rows as REC completes (rolling, interleaved with X3–X6) | ~105–120 | all | per-row |
| **X8** | B4/B6 sweep: statements for the X0c-enumerated derived rows + parked-vague records with concrete handles | pinned at X0c | per-parent | per-row |
| **X9** | Decision-gated: B5 out-of-scope tail if D1 says go (needs `combinatorics-misc` package + `rocq-mathcomp-field`) | 0–120 | new | F_q, sumsets, convexity |

Acceptance per wave = v1 gate: `check_milestone.py <phase> <pkg>` green, overlay
updated, `CORPUS_STATUS.md` regenerated, faithfulness techniques #1–#4 applied,
mutants added for new load-bearing definitions, **plus** v2's source-verification and
SVER pre-landing checks.

**v2 statement-complete target:** every tracked row — S2, S5, derived, and **all**
S6 clusters — is resolved: statement-owing rows (B2/B3 survivors, S5 non-alias, S6
`promoted`, derived) reach done / partial / blocked-with-note; alias, edge-anchor,
and parked rows carry their disposition + note. The v1 "attempted = total" standard,
extended over the full six-source universe.

---

## 5. Theorem & certificate track (phase codes T1–T3) — the S4 payoff

v1 was statements-only. S4's folders contain *hand-proved theorems with written
proofs*, refuted sub-conjectures with explicit counterexamples, and exact-arithmetic
certificate corpora. Formalizing these turns area packages from statement catalogs
into theorem-bearing libraries. Runs interleaved with statement waves; each item is
its own milestone with the same gates (all Qed, no Admitted, Print Assumptions clean).
**Every T-milestone re-snapshots its folder's ledger at start** — the folders are
active research; the list below is the 2026-07-07 state.

**T1 — hand-proved theorems (highest value, ordered by fit):**

1. Pebbling: Weight Function Lemma + certificate-sum corollary; replay the 22 rational
   certificates → formal `π(L□L) ≤ 246` and rooted `≤ 106` (pure ℚ arithmetic; ideal).
2. Tournament criticality: P13 (AC_n 3-ω⃗-critical, all odd n ≥ 7), P18, P20 —
   infinite-family theorems with explicit constructions; + two-free-colours lemma,
   ω⃗ subadditivity, substitution laws (serves both 2310.04265 folders; check the
   ledger for the newer P21–P23 layer at milestone start).
3. Matching-FAS ∈ P: Theorem 1 + Lemmas 2–5 + 2-SAT reduction correctness
   (complete written proof stack in `docs/lemmas.md`; non-novel but load-bearing).
4. Directed path δ=3 for all n ≥ 7 + corrected Cheng–Keevash Lemma 7 (the published
   proof had a silent arc/vertex swap — formalization is the fix's natural home).
5. Two-extremal structural lemmas T1/T2/T4/P3/P6 + P1 (H2 ⊆ 2-extremal) — feeds the
   X2 statement of AAC Conjecture 9.2.
6. Heroic tower: substitution identity + χ_d(D_k) = k (the H2 disproof engine).
7. 3-decomposition Lemma 1 (bridge reduction); Hoffmann-Ostenhof vertex-type identity.
8. Earth–moon: Heawood χ_EM ≤ 12 via 11-degeneracy; K6+C5 biplanar witness + χ = 9.
9. Crossing: D8 witness identity (ℚ(δ) algebra), Ore-congruence emptiness of
   (25,48)/(26,50); D16 inequality chain (medium).
10. SAD: CL1 bilateral lifting lemma (combinatorial, arborescence-based); EC-log
    theorem (C=6, n₀=3) — heavier (cut-counting + first-moment, finitizable).

**T2 — refutation certificates** (each anchors to a `status: disproved` row created
in X0c/X8 — T2 appends the `~ statement` proof, never creates a competing row):
Conjecture L (4-vertex funnel counterexample);
Antichain Coverage at n=12 (10 sides + trace sets); D15 (Voigt planar χ_ℓ=5 vs
cr(K5)=1); H19 tower arithmetic (given the cited pod theorem as hypothesis); Jain's
2nd conjecture — port Ulyanov's 36-point Lean 4 `bv_decide` obstruction to Rocq;
Chen–Chvátal P2 (bridge→path infinite family of pendant bad graphs).

**T3 — mechanical certificate replays (larger, tool-gated):** D25 3-dicriticality
(25 vertices); k4_n10 (3,664 completions); LFO obstruction corpora (18/572/5,560);
F6=45 UNSAT ledger; L3..L7 H2-membership witnesses (52 digraphs); F0 bad-graph census
n ≤ 10; **snark S²-flow n ≤ 28 via ~3,247 Krawczyk interval certificates** — heaviest,
requires an interval-arithmetic dependency (e.g. `coq-interval`); the certificates
live under `problems/unit_vector_flows/data/` (the top-level `data/interval_certs/`
is empty — see D5); schedule last, decision D3.

---

## 6. Edges & atlas

S2/S5 papers assert many implications (2403.02298 Conj 3 ⟹ Conj 4; blow-up chains in
2410.23566; Gyárfás–Sumner equivalences). Record them as `@EDGE` annotations during
statement waves; Qed relative theorems where the derivation is elementary.
Cross-corpus edges (arXiv ⟺ OPG ⟺ erdős: Mader 1985, directed Gyárfás–Sumner,
Sidorenko-in-tournaments, EFL = erdős #19…) are the first real content for the
`atlas/` scaffold. The S6 studies-slice is the systematic feedstock: "paper P studies
C, proving R" becomes an edge from P's conjecture rows to C. Prerequisites: the §3
item-2 edge-graph fix (today, digraph-hosted cross-corpus edges are silently dropped)
and the canonical `row_id` identity (§1.4) — with four corpora plus alias rows,
`formal_name` alone is ambiguous; every edge endpoint normalizes to a canonical row
before the graph is built or checked.

---

## 7. Open decisions (defaults chosen; flag disagreement)

- **D1 — non-graph tail (77–120 records).** Default: rows-with-defer
  (`out-of-scope-v2`), no statements in v2 waves; revisit after X6/XE. Alternative:
  `combinatorics-misc` package + `rocq-mathcomp-field` in X9.
- **D2 — Informal records (186).** Default: per-record triage in X0b; expect a
  substantial fraction salvageable to B2/B3, rest parked B4 with notes. Alternative:
  park all 186 wholesale (cheaper, loses real conjectures hidden in Informal).
- **D3 — Krawczyk replay (~3,247 certificates).** Default: in-plan but last (T3
  tail), gated on a `coq-interval` spike + count verification against
  `problems/unit_vector_flows/data/`. Alternative: out of scope for v2.
- **D4 — theorem-track priority.** Default: interleave **only** the directed T1
  items 2/3/4/5/6 — they share definitions with the X1/X2 statements and de-risk
  them; everything else in the T-track (T1 items 1/7/8/9/10, T2, T3) is
  post-statement-complete backlog, T3 additionally spike-gated (§8).
  Statement-completeness remains the headline milestone. Alternatives:
  statements-first strictly (no interleaving), or pull T1 item 1 (pebbling —
  self-contained, high-value) forward if capacity allows.
- **D5 — problems/ housekeeping (upstream repo, owner action).** ~22 GB stray
  shell-redirect files (`:`, `:20`, `:24`) in `chen_chvatal_lines_plus_bridges/`;
  `unvd_vertex_deletion/` is a stub (no README/ledger) and 8 further folders have no
  `ledger.json` (doc-mining fallback in B6 covers them); the top-level
  `data/interval_certs/nontrivial_n10_to_26/` is empty; `PROBLEMS_OVERVIEW.md` covers
  8 of 19 folders and is 6+ weeks stale; conflicting attribution for arXiv:1606.06011
  between the twin Chen–Chvátal folders.
- **D6 — S5 erdosproblems corpus in scope?** Default: **yes** — it is a curated,
  statement-bearing corpus inside `graph-conjectures`, squarely under the stated
  goal; XE waves as scheduled. Alternative: explicit scope-out with documented
  reason (then the goal statement must be narrowed).
- **D7 — S6 statement-promotion bar.** That every S6 cluster gets a tracked row is
  settled (X0d — required by the headline goal); the open decision is only the
  promotion bar. Default: promote named third-party conjectures with self-contained
  statements to statement-owing rows; the rest stay tracked as alias / edge-anchor /
  parked. Alternative: a more aggressive bar (any self-contained statement).

---

## 8. Milestone schedule, releases, effort model

v1 landed 227 rows in ~33 milestones. v2 is ~1,700+ tracked rows (227 v1 frozen +
1,039 S2/S5 + ~669 S6 clusters + derived) with ~600–850 statement targets after
triage (S2 ~440–580 + S5 ~150–250 + derived/S6 promotions), discounted by the X1
reconciliation and mature foundations. Working estimate: **~25–30 statement
milestones + the honestly-sized T-track below**, sequenced:

1. **M-V2-START** = X0a (schema, routing, gates, licensing — **no v2 rows yet**) →
   X0b (S2/S5 rows created; every count in this plan pinned to an exact,
   reproducible number, bucket regexes committed alongside). X0c and X0d are
   separate milestones that run in parallel with early waves: X0c before X8 and
   before any T2 work; X0d before the S6-promotion/atlas waves.
2. X1 → X2 (directed, with **only** the de-risking directed T1 items 2/3/4/5/6
   interleaved — they share definitions with these waves' statements).
3. X3 → X4 → X5 (undirected mass), X7 rolling.
4. XE1–XE2 (erdős corpus), X6.
5. X8, then the readback/review pass (techniques #5/#6) over the whole v2 corpus —
   at this scale a standing per-wave step, not a one-shot.
6. Decision gates: D1/X9.
7. **M-V2-STATEMENT-COMPLETE** release.
8. Post-release T-track backlog: remaining T1 items (1/7/8/9/10) and the T2 batch;
   **T3 is explicitly post-statement-complete** and gated on spikes (a
   `coq-interval` feasibility spike for the Krawczyk replay; a certificate-replay
   harness spike for the large corpora). Items that fail their spike are dropped
   from v2 with a note, not silently carried.

**T-track sizing (revised — "~10 milestones" was optimistic).** The ten T1 items are
roughly one milestone each; T2 is 2–3 batches; T3 items are individually
milestone-sized (2-SAT reduction correctness, interval arithmetic, a Lean-4→Rocq
port, multi-thousand-instance replays). Fully executed, the T-track is **~15–20
milestones**; only the 4–5 de-risking directed T1 items sit on the
statement-complete critical path — the rest is post-release backlog by default (D4).

**Release policy (new).** Tag per completed wave (`v2.0.0-x1`, `v2.0.0-x3`, …);
manifest carries `schema_version`; `CORPUS_STATUS.md` regeneration is the changelog
(including status flips from SVER re-sweeps); README badge shows per-corpus
attempted/total from X0b onward, not only at the end.

**Risks.** Extraction noise (mitigated by REC + source-verification + the
faithfulness stack — the reason v2 has new gates); status drift in a living
literature (SVER pre-landing + quarterly re-sweeps); scope creep from derived rows
(X0c-pinned enumeration; additions require a manifest change, not ad-hoc files);
tooling debt underestimation (§3 lists audited, code-verified costs — the three
oversold rev-1 claims are corrected there); gate runtime growth (§3 item 9);
single-maintainer bandwidth (waves are independent — pausing between milestones
leaves the repo green, exactly as in v1).
