#!/usr/bin/env python3
"""Build meta/v2_corpus_manifest.json + meta/v2_legs_state.json (milestone X0b; plan §1).

Mechanical, deterministic construction of the v2 corpus rows from the upstream
graph-conjectures clone (path via $GRAPH_CONJECTURES, default sibling of this repo's parent):

  S2  data/arxiv_conjectures.json      762 arXiv statement records -> corpus "arxiv"
      data/arxiv_reviews/*.json        per-record status (open/partial/solved/disproved/unclear)
      ARXIV_OPEN_DIFFICULTY_RANKING.md difficulty score/tier/lean (metadata, never scheduling)
      data/arxiv_opg_matches.json      manual_confirmed paper->OPG matches (B1 alias CANDIDATES —
                                       flagged for per-record adjudication, never auto-aliased)
  S5  data/erdos_graph.json            277 erdosproblems.com records -> corpus "erdos"
      data/intersection.json           15 erdos<->OPG crosswalk entries -> alias_of rows

Status mapping (exact-type-gate vocabulary, plan §1.4): identity for open/partial/solved/
disproved; `unclear` -> open (safest polarity: forbids committed direct proofs); the raw review
status is preserved in `review_status`. The three ABOULKER_CONJECTURES_RANKED.md errata status
corrections are applied explicitly (ERRATA below) since the review files predate them.

Recovery triage (plan §1.1 B3) is pinned HERE so the counts are reproducible:
  needed  iff statement_text is missing, shorter than SHORT_LEN chars, or matches INTERNAL_RE.

Classifier-owned fields (bucket, topic, formalizability, repo, phase, formal_name, rocq_idiom,
new_primitives, defer_reason, disposition) are initialized to None — the X0b classifier pass and
wave planning fill them; this builder is re-runnable without clobbering them ONLY via the overlay
model (legs live in v2_legs_state.json and are merged in, like the v1 builder). The verification
tuple (source_verified_by/at, implemented_by, verification_note) starts empty; source_locator +
source_hash are prefilled mechanically (they identify the consulted record, not its verification).

Usage: python3 meta/build_v2_manifest.py [--check]     (--check: fail on drift vs committed)
"""
import glob
import hashlib
import json
import os
import re
import subprocess
import sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG

GC = os.environ.get("GRAPH_CONJECTURES",
                    os.path.join(os.path.dirname(os.path.dirname(MONO)), "graph-conjectures"))
if not os.path.isdir(GC):
    GC = os.path.expanduser("~/Recherche/graph-conjectures")

OUT_MANIFEST = REG.manifest_path("v2")
OUT_OVERLAY = REG.overlay_path("v2")

# ── pinned triage constants (plan §1.1 B3; change = manifest change, reviewably) ──
SHORT_LEN = 59
INTERNAL_RE = re.compile(
    r"\b(Theorem|Lemma|Corollary|Conjecture|Question|Problem|Proposition|Claim|Section|Equation)\s+\d")
STATUS_MAP = {"open": "open", "partial": "partial", "solved": "solved",
              "disproved": "disproved", "unclear": "open"}

# ── S3 errata status corrections (ABOULKER_CONJECTURES_RANKED.md, revised draft 2026-05-21) ──
ERRATA = [
    ("2310.04265", "Conjecture 4.3 (Gyárfás-Sumner for Tournaments)", "disproved",
     "Errata (Aboulker ranked list): refuted by Aubian arXiv:2401.07776 — forest backedge graph "
     "with bounded clique number and unbounded dichromatic number."),
    ("1710.06282", "Conjecture 1.4", "solved",
     "Errata (Aboulker ranked list): treewidth version follows from Conjecture 1.2 "
     "(Cames van Batenburg–Huynh–Joret–Raymond) + the grid-minor theorem."),
    ("2310.04265", "Conjecture 5.6", "solved",
     "Errata (Aboulker ranked list): implied by Crew–Fan–Koerts–Moore–Spirkl arXiv:2602.09863 "
     "plus dom(T) <= omega-bar(T)."),
]


def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def sha256_text(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def git_head(path):
    try:
        return subprocess.run(["git", "-C", path, "rev-parse", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
    except OSError:
        return ""


# ── load sources ──
arxiv = json.load(open(os.path.join(GC, "data", "arxiv_conjectures.json")))
erdos = json.load(open(os.path.join(GC, "data", "erdos_graph.json")))
intersection = json.load(open(os.path.join(GC, "data", "intersection.json")))
matches = json.load(open(os.path.join(GC, "data", "arxiv_opg_matches.json")))

reviews = {}    # (arxiv_id, conjecture_title) -> review dict
untitled = {}   # arxiv_id -> [review dicts with null conjecture_title] (rare extractor gap)
for fn in sorted(glob.glob(os.path.join(GC, "data", "arxiv_reviews", "*.json"))):
    rv = json.load(open(fn))
    rv["review_id"] = os.path.basename(fn)[:-5]   # filename is authoritative (key not always present)
    if not rv.get("conjecture_title"):
        untitled.setdefault(rv.get("arxiv_id"), []).append(rv)
        continue
    key = (rv.get("arxiv_id"), rv.get("conjecture_title"))
    if key in reviews:
        sys.exit(f"duplicate review key {key} ({fn})")
    reviews[key] = rv

# difficulty score/tier/lean from the Complete Ranking table, keyed by review_id
RANK_RE = re.compile(r"^\|\s*\d+\s*\|\s*([\d.]+)\s*\|\s*(\d)\s*\|\s*(\w+)\s*\|\s*\w+\s*\|\s*`?([\w.\-]+__\d+)`?\s*\|")
ranking = {}
for line in open(os.path.join(GC, "ARXIV_OPEN_DIFFICULTY_RANKING.md")):
    m = RANK_RE.match(line)
    if m:
        ranking[m.group(4)] = {"score": float(m.group(1)), "tier": int(m.group(2)), "lean": m.group(3)}

accepted_match = {aid: m["opg_slug"] for aid, m in matches.items() if m.get("manual_confirmed")}

# classification merge (X0b classifier pass): meta/v2_classification.json is the committed
# output of the classifier workflow, keyed by slug -> {bucket, topic, formalizability,
# defer_reason, repo, b1_adjudication, duplicate_of_hint, class_notes}. The builder merges it
# so the manifest stays a pure deterministic function of committed inputs.
CLASS_PATH = os.path.join(META, "v2_classification.json")
CLASS = json.load(open(CLASS_PATH))["rows"] if os.path.exists(CLASS_PATH) else {}
CLASS_FIELDS = ("bucket", "topic", "formalizability", "defer_reason", "repo",
                "b1_adjudication", "duplicate_of_hint", "class_notes")

# overlay merge model (v1 convention): legs live in the overlay; the builder merges them in.
prior_overlay = REG.load_overlay("v2", required=False) or {"entries": {}}
prior_entries = prior_overlay.get("entries", {})

LEGS = ["statement", "grounding", "edges", "correspondence", "audit_page"]


def legs_for(slug):
    e = prior_entries.get(slug, {})
    return {lg: e.get(lg, "todo") for lg in LEGS}


def recovery_of(stmt):
    if not stmt or not stmt.strip():
        return "needed"
    if len(stmt) < SHORT_LEN or INTERNAL_RE.search(stmt):
        return "needed"
    return "none"


rows = []
missing_reviews = []

# ── S2: arXiv rows ──
per_paper_idx = {}
errata_by_key = {(a, t): (st, note) for a, t, st, note in ERRATA}
errata_hit = set()
for rec in arxiv:
    aid = rec["arxiv_id"]
    nn = per_paper_idx.get(aid, 0)
    per_paper_idx[aid] = nn + 1
    key = (aid, rec["title"])
    rv = reviews.get(key)
    if rv is None:
        # fallback: a same-paper review whose conjecture_title the extractor left null —
        # join only when it is unambiguous (exactly one such review for this paper).
        cands = untitled.get(aid, [])
        if len(cands) == 1:
            rv = cands[0]
        else:
            missing_reviews.append(key)
            continue
    raw_status = rv.get("status", "")
    status = STATUS_MAP.get(raw_status)
    note = None
    if key in errata_by_key:
        status, note = errata_by_key[key][0], errata_by_key[key][1]
        errata_hit.add(key)
    if status is None:
        sys.exit(f"unmapped review status {raw_status!r} for {key}")
    rid = f"arxiv:{aid}#{nn:02d}"
    slug = f"axv_{aid.replace('.', '_')}_{nn:02d}"
    frag = (rec.get("statement_text") or "") + "\n" + (rec.get("context_text") or "")
    rank = ranking.get(rv.get("review_id", ""), {})
    rows.append({
        "row_id": rid, "slug": slug, "corpus": "arxiv",
        "record_key": f"{aid}__{nn:02d}", "kind": rec.get("kind"),
        "title": rec["title"], "arxiv_id": aid, "erdos_id": None,
        "paper_title": rec.get("paper_title"), "paper_authors": rec.get("paper_authors"),
        "published": rec.get("published"), "abs_url": rec.get("abs_url"),
        "attributed_to": rec.get("attributed_to"), "attributed_year": rec.get("attributed_year"),
        "statement_text": rec.get("statement_text"), "context_text": rec.get("context_text"),
        # source_text starts as the extractor's statement (to be REPLACED by our normalized
        # statement at REC/implementation time — plan §2 licensing: store normalized).
        "source_text": rec.get("statement_text") or None,
        "source_locator": f"arXiv:{aid} — {rec['title']}",
        "source_hash": sha256_text(frag),
        "source_excerpt": None, "license": None,
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": status,
        "status_semantics": (note or (rv.get("summary") if status != "open" else None)),
        "review_status": raw_status, "review_date": rv.get("reviewed_at"),
        "review_confidence": rv.get("confidence"), "extraction_confidence": rec.get("confidence"),
        "difficulty_score": rank.get("score"), "difficulty_tier": rank.get("tier"),
        "difficulty_lean": rank.get("lean"),
        "recovery": recovery_of(rec.get("statement_text")),
        "b1_candidate": aid in accepted_match,
        "opg_match": accepted_match.get(aid),
        "alias_of": None, "parent": None, "disposition": None,
        # classifier / wave-planning fields (X0b classifier + wave milestones fill these):
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        "legs": legs_for(slug),
    })

if missing_reviews:
    sys.exit(f"{len(missing_reviews)} arXiv records lack a review (join on arxiv_id+title): "
             f"{missing_reviews[:5]}")
if errata_hit != set(errata_by_key):
    sys.exit(f"errata records not found in corpus: {set(errata_by_key) - errata_hit}")

# ── S5: erdős rows (aliases per intersection.json) ──
erdos_alias = {}   # erdos number -> opg slug
for opg_slug, m in intersection.items():
    erdos_alias[int(m["erdos_id"])] = opg_slug
for rec in sorted(erdos, key=lambda r: r["number"]):
    n = rec["number"]
    rid = f"erdos:{n}"
    slug = f"erdos_{n}"
    alias = erdos_alias.get(n)
    stmt = rec.get("statement", "")
    row = {
        "row_id": rid, "slug": slug, "corpus": "erdos",
        "record_key": str(n), "kind": "Problem",
        "title": f"Erdős problem #{n}", "arxiv_id": None, "erdos_id": n,
        "abs_url": rec.get("url"), "tags": rec.get("tags"), "prize": rec.get("prize"),
        "citation_keys": rec.get("citation_keys"),
        "statement_text": stmt, "context_text": None,
        "source_text": stmt or None,
        "source_locator": rec.get("url"),
        "source_hash": sha256_text(stmt),
        "source_excerpt": None, "license": "GFDL (erdosproblems.com, attribution Thomas Bloom)",
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": rec.get("status"),
        "status_semantics": None,
        "review_status": rec.get("status"), "review_date": None,
        "recovery": recovery_of(stmt),
        "b1_candidate": False, "opg_match": alias,
        "alias_of": (f"opg:{alias}" if alias else None),
        "parent": None, "disposition": None,
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        "legs": legs_for(slug) if not alias else {lg: "todo" for lg in LEGS},
    }
    if rec.get("status") not in ("open", "solved"):
        sys.exit(f"unexpected erdos status {rec.get('status')!r} for #{n}")
    rows.append(row)

# merge classifier output (fields the classifier owns; None until it has run)
for r in rows:
    c = CLASS.get(r["slug"], {})
    for f in CLASS_FIELDS:
        r.setdefault(f, None)
        if c.get(f) is not None:
            r[f] = c[f]
    # parked buckets carry their disposition from day one (plan §4: parked rows count as
    # attempted via disposition + note; the note is the classifier's defer_reason)
    if r.get("bucket") in ("B4", "B5") and not r.get("disposition"):
        r["disposition"] = "parked"

rows.sort(key=lambda r: r["row_id"])
slugs = [r["slug"] for r in rows]
assert len(slugs) == len(set(slugs)), "duplicate slug"
assert len(rows) == len({r["row_id"] for r in rows}), "duplicate row_id"

# ── totals ──
def cnt(key):
    out = {}
    for r in rows:
        out[str(r.get(key))] = out.get(str(r.get(key)), 0) + 1
    return dict(sorted(out.items()))

n_alias = sum(1 for r in rows if r["alias_of"])
totals = {
    "rows": len(rows), "by_corpus": cnt("corpus"), "by_status": cnt("status"),
    "by_kind": cnt("kind"), "by_recovery": cnt("recovery"),
    "alias_rows": n_alias, "b1_candidates": sum(1 for r in rows if r["b1_candidate"]),
    "arxiv_rows": sum(1 for r in rows if r["corpus"] == "arxiv"),
    "erdos_rows": sum(1 for r in rows if r["corpus"] == "erdos"),
}

manifest = {
    "_README": "v2 corpus manifest (graph-conjectures beyond OPG; plan meta/V2_FULL_CORPUS_PLAN.md). "
               "Built by meta/build_v2_manifest.py from the upstream graph-conjectures clone — "
               "deterministic; regenerate + diff to review changes. Status uses the exact-type-gate "
               "vocabulary (unclear->open, raw kept in review_status; 3 Aboulker errata applied). "
               "b1_candidate rows are OPG-alias CANDIDATES pending per-record adjudication. "
               "source_text currently holds the extractor's statement; REC/implementation replaces it "
               "with our normalized statement (licensing: LICENSE-DATA.md). Legs merge in from "
               "meta/v2_legs_state.json (the source of truth). Classifier fields (bucket/topic/"
               "formalizability/repo/phase/formal_name) are filled by the X0b classifier pass and "
               "wave planning, recorded via meta/apply_v2_classification.py.",
    "schema_version": 1,
    "provenance": {
        "graph_conjectures_commit": git_head(GC),
        "arxiv_conjectures_sha256": sha256_file(os.path.join(GC, "data", "arxiv_conjectures.json")),
        "erdos_graph_sha256": sha256_file(os.path.join(GC, "data", "erdos_graph.json")),
        "intersection_sha256": sha256_file(os.path.join(GC, "data", "intersection.json")),
        "arxiv_opg_matches_sha256": sha256_file(os.path.join(GC, "data", "arxiv_opg_matches.json")),
        "n_reviews_joined": len(reviews),
    },
    "totals": totals,
    "rows": rows,
}
new = json.dumps(manifest, ensure_ascii=False, indent=1) + "\n"

# overlay init: every NON-ALIAS row gets an entry (alias rows own nothing — plan §1.4)
overlay = {
    "_README": "Per-row leg-state overlay for the v2 corpus (source of truth for legs; the manifest "
               "merges it in at build time). Same conventions as opg_legs_state.json: non-todo legs "
               "require commit+package provenance and a note; statement=done additionally requires "
               "the source-verification tuple on the manifest row (gated by check_milestone.py).",
    "_allowed_states": ["todo", "partial", "done", "blocked"],
    "_legs": LEGS,
    "entries": {r["slug"]: prior_entries.get(r["slug"], {lg: "todo" for lg in LEGS})
                for r in rows if not r["alias_of"]},
}
new_overlay = json.dumps(overlay, ensure_ascii=False, indent=1) + "\n"

if "--check" in sys.argv:
    old = open(OUT_MANIFEST).read() if os.path.exists(OUT_MANIFEST) else ""
    old_ov = open(OUT_OVERLAY).read() if os.path.exists(OUT_OVERLAY) else ""
    if old != new or old_ov != new_overlay:
        sys.exit("V2-MANIFEST DRIFT: regenerate with `python3 meta/build_v2_manifest.py`")
    print(f"v2-manifest gate OK: {totals['rows']} rows ({totals['by_corpus']}), no drift")
else:
    open(OUT_MANIFEST, "w").write(new)
    open(OUT_OVERLAY, "w").write(new_overlay)
    print(f"wrote {os.path.relpath(OUT_MANIFEST, MONO)}: {totals['rows']} rows "
          f"| by_corpus {totals['by_corpus']} | by_status {totals['by_status']} "
          f"| recovery {totals['by_recovery']} | aliases {n_alias} | b1 {totals['b1_candidates']}")
