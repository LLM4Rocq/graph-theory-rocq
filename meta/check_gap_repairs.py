#!/usr/bin/env python3
"""Compile fixed partial-proof artifacts; grant no source-resolution exemption.

The source conjectures remain unresolved by these lemmas. Their correspondence
and remaining obligations are documented in meta/GAP_REPAIRS.md.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile

import formal_resolutions as BUILD
import rocq_toolchain as ROCQ

ROOT = Path(__file__).resolve().parent.parent
PACKAGE = "chromatic-theory"
UNPROVED = re.compile(r"\b(?:Admitted|Axiom|Axioms|Parameter|Parameters|Conjecture|admit)\b")
# Keep this dependency order: every artifact is recompiled from current source.
SOURCES = (
    "theories/applications/gap_repairs/viable_boundary.v",
    "theories/applications/gap_repairs/frozen_coloring_core.v",
    "theories/applications/gap_repairs/frozen_coloring_switch.v",
    "theories/applications/gap_repairs/frozen_coloring_fiber.v",
    "theories/applications/gap_repairs/frozen_coloring_graph.v",
    "theories/applications/gap_repairs/frozen_coloring_recolor.v",
    "theories/applications/gap_repairs/frozen_coloring_bound.v",
    "theories/applications/gap_repairs/frozen_coloring_greedy.v",
    "theories/applications/gap_repairs/frozen_coloring_resolution.v",
)
PROBE = r"""
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import viable_boundary
  frozen_coloring_core frozen_coloring_recolor frozen_coloring_bound
  frozen_coloring_greedy frozen_coloring_resolution.
Check (six_cycle_precoloring_viable :
  viable (fun u v : boundary => is_true (u -- v)) boundary_hue boundary_color).
Check (six_cycle_precoloring_viable_swapped :
  viable (fun u v : boundary => is_true (u -- v)) boundary_hue_swapped boundary_color).
Check (@fc_frozen_isolated_iff : forall (G : sgraph) (C : finType)
  (f : fc_coloring G C), fc_proper f -> fc_frozen f = fc_isolated f).
Check (@fc_frozen_count_bound : forall (G : sgraph) (C : finType),
  (forall x : G, #|fc_closed x| <= #|C|) ->
  connected [set: G] -> ~ clique [set: G] ->
  (#|G| + 4) * #|[set f : fc_coloring G C | fc_frozen_proper f]| <=
  4 * #|[set f : fc_coloring G C | fc_proper f]|).
Check (@fc_frozen_count_quantitative : forall (G : sgraph) (C : finType),
  (forall x : G, #|fc_closed x| <= #|C|) ->
  connected [set: G] -> ~ clique [set: G] -> forall k,
  4 * k <= #|G| ->
  k * #|[set f : fc_coloring G C | fc_frozen_proper f]| <=
  #|[set f : fc_coloring G C | fc_proper f]|).
Check (@fc_proper_exists : forall (G : sgraph) (C : finType) (c0 : C),
  (forall x : G, #|fc_closed x| <= #|C|) ->
  exists f : fc_coloring G C, fc_proper f).
Check (@fc_delta_proper_positive : forall G : sgraph, 0 < fc_delta_proper_count G).
Check (@fc_delta_frozen_count_bound : forall G : sgraph,
  connected [set: G] -> ~ clique [set: G] ->
  (0 < fc_delta_proper_count G) /\
  ((#|G| + 4) * fc_delta_frozen_count G <= 4 * fc_delta_proper_count G)).
Check (@fc_delta_frozen_count_quantitative : forall G : sgraph,
  connected [set: G] -> ~ clique [set: G] -> forall k,
  4 * k <= #|G| -> k * fc_delta_frozen_count G <= fc_delta_proper_count G).
Check (@fc_delta_isolated_count_bound : forall G : sgraph,
  connected [set: G] -> ~ clique [set: G] ->
  (0 < fc_delta_proper_count G) /\
  ((#|G| + 4) * fc_delta_isolated_count G <= 4 * fc_delta_proper_count G)).
Print Assumptions six_cycle_precoloring_viable.
Print Assumptions six_cycle_precoloring_viable_swapped.
Print Assumptions fc_frozen_isolated_iff.
Print Assumptions fc_frozen_count_bound.
Print Assumptions fc_frozen_count_quantitative.
Print Assumptions fc_proper_exists.
Print Assumptions fc_delta_proper_positive.
Print Assumptions fc_delta_frozen_count_bound.
Print Assumptions fc_delta_frozen_count_quantitative.
Print Assumptions fc_delta_isolated_count_bound.
"""


def check(root: Path) -> str:
    root = root.resolve()
    flags, listed = BUILD.project(root, PACKAGE)
    for source in SOURCES:
        relative = f"{PACKAGE}/{source}"
        path = BUILD.local_file(root, relative)
        if relative not in listed:
            raise BUILD.ResolutionError(f"repair source missing from _CoqProject: {relative}")
        clean = BUILD.CONTRACTS.strip_comments(path.read_text())
        if UNPROVED.search(clean):
            raise BUILD.ResolutionError(f"forbidden admission/axiom in repair source: {relative}")
    directory = root / PACKAGE
    env = ROCQ.environment()
    BUILD.build_dependencies(root, PACKAGE, env, set())
    BUILD.run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"], directory, env)
    BUILD.run(["make", "-f", "Makefile.coq", *[str(Path(s).with_suffix(".vo")) for s in SOURCES]],
              directory, env)
    for source in SOURCES:
        BUILD.run(["rocq", "compile", *flags, source], directory, env)
    with tempfile.TemporaryDirectory(prefix="rocq-gap-repairs-") as temporary:
        probe = Path(temporary) / "GapRepairCheck.v"
        probe.write_text(PROBE)
        output = BUILD.run(["rocq", "compile", *flags, str(probe)], directory, env)
    if "Axioms:" in output or output.count("Closed under the global context") != 10:
        raise BUILD.ResolutionError(f"repair theorem assumptions are not closed:\n{output}")
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        output = check(args.root)
        if args.report:
            args.report.write_text(output)
    except (BUILD.ResolutionError, RuntimeError) as exc:
        print(f"gap-repair checks FAILED: {exc}", file=sys.stderr)
        return 1
    print("gap-repair artifacts OK (10 exact, assumption-free lemmas; no new source resolutions)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
