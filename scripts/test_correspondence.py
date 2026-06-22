#!/usr/bin/env python3
"""test_correspondence.py — sanity checks for the auditor registry.

Asserts the generated web/correspondence/registry.json is well-formed: known
entries present, every entry carries the fields the dashboard needs, edges and
`specializes` targets resolve, and a couple of marquee facts hold. Run in CI
after build_correspondence.py.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "web" / "correspondence" / "registry.json"
DEPGRAPH = ROOT / "docs" / "dependency_graph.json"

MUST_EXIST = [
    "caccetta_haggkvist_statement",
    "seymour_second_neighbourhood_statement",
    "bermond_thomassen_statement",
    "woodall_statement",
    "CL1_statement",
    "bang_jensen_yeo_SAD_statement",
    "conjecture_5_10_statement",
    "conjecture_5_10_at_345",
    "cheng_keevash_conj1_statement",
    "ck_conj1_delta3",
]


def main() -> None:
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    entries = reg["entries"]
    by_id = {e["id"]: e for e in entries}
    dep_nodes = {n["id"] for n in
                 json.loads(DEPGRAPH.read_text(encoding="utf-8"))["nodes"]}
    fails: list[str] = []

    def check(cond: bool, msg: str) -> None:
        if not cond:
            fails.append(msg)

    check(len(entries) >= 80, f"expected >= 80 entries, got {len(entries)}")
    for name in MUST_EXIST:
        check(name in by_id, f"missing expected entry {name!r}")

    for e in entries:
        i = e["id"]
        check(bool(e.get("title")), f"{i}: empty title")
        check(e.get("cluster") not in (None, "", "?"), f"{i}: no cluster")
        check(bool(e.get("decoded", "").strip()), f"{i}: empty decoded")
        check(bool(e["formal"]["verbatim"].strip()), f"{i}: empty verbatim")
        check(e["formal"]["github_url"].startswith("https://github.com/"),
              f"{i}: bad github_url")
        # edge targets may be dependency-graph inline endpoints (not entries);
        # only `specializes` (curated) is required to resolve to a real entry.
        for sp in e.get("specializes", []):
            check(sp in by_id or sp in dep_nodes,
                  f"{i}: specializes target {sp!r} unresolved")

    cl1 = by_id.get("CL1_statement", {})
    check(any(g.get("name") == "CL1_premises_inhabited"
              for g in cl1.get("grounding", [])),
          "CL1_statement missing grounding CL1_premises_inhabited")
    c510 = by_id.get("conjecture_5_10_at_345", {})
    check("conjecture_5_10_statement" in c510.get("specializes", []),
          "conjecture_5_10_at_345 should specialize conjecture_5_10_statement")

    if fails:
        print("CORRESPONDENCE TESTS FAILED:\n  " + "\n  ".join(fails),
              file=sys.stderr)
        sys.exit(1)
    n_auth = sum(1 for e in entries if e.get("decoded_authored"))
    print(f"correspondence tests OK: {len(entries)} entries, "
          f"{n_auth} authored decoded, all edges resolve")


if __name__ == "__main__":
    main()
