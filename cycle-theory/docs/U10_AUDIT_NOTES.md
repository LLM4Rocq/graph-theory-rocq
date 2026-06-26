# cycle-theory / U10 — Berge–Fulkerson / Petersen colouring audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; 2nd cycle-theory milestone
(joins U6). Verified: compiles axiom-free, 22/22 grounding lemmas `Qed`, `check_milestone U10` →
ACCEPTED. **Faithfulness: 3/3 OK, 0 flagged.** Leg state: **3 done, 0 blocked.**

## Reuse (confirms the deferred `is_matching` decision)
U10 **imports U6** (`From Cycle.conjectures Require Import U6`) and reuses `cubic`, `bridgeless`,
`subdeg`, `cut`, `mdeg`, **`is_matching`** verbatim — *intra-area* sharing, not a 2nd-area trigger. So
keeping the (mgraph) `is_matching` local to cycle-theory was correct; `is_perfect_matching` here just
sharpens it (`subdeg M v = 1` vs `≤ 1`). The **Petersen graph** is built directly as the Kneser graph
KG(5,2) — `petersenV := {x : {set 'I_5} | #|x| == 2}` (an honest 10-vertex finType), adjacency =
disjointness — since neither base nor coq-graph-theory has Petersen/Kneser.

## SECOND verified edge (sound + honest): `petersen_coloring ⟹ berge_fulkerson`
`Theorem petersen_coloring_implies_berge_fulkerson : external_petersen_BF_cover_statement ->
petersen_coloring_statement -> the_berge_fulkerson_statement` (Qed). Checked carefully after the
Seymour lesson:
- **Endpoints faithful** (audit-confirmed): BF = `exists L, perfect_matching_cover 6 L` (6 perfect
  matchings, each edge in exactly 2); Petersen colouring = a structure-preserving edge map
  `f : edge G -> Pedge` taking mutually-adjacent G-edge triples to mutually-adjacent Petersen-edge
  triples. Both guarded by `0 < #|G|` + `cubic_bridgeless`.
- **Honest external dependency:** the implication is Qed-closed *relative to* the explicitly named
  `external_petersen_BF_cover_statement` (the Petersen graph's own six perfect matchings, pulled back
  along `f`; Jaeger 1985) — disclosed in the `(*@EDGE*)` note, **never `Admitted`**. This is the
  plan's `external_<x>` pattern, not a weakening. Kept `status=verified`.

## Candidate edges
`berge_fulkerson ⟹ intersecting_two_perfect_matchings` and `petersen_coloring ⟹ intersecting…` —
both candidate, not forced.

## Nits (cosmetic, no change required)
- `mut_adj3 (r : rel T) a b c := [&& r a b, r b c & r a c]` is carrier-agnostic (used over both
  `line_rel` and `Padj`) — a cross-area-shaped combinator left area-local + untagged; tag
  `[@MOVE-to-base]` if a 2nd area ever needs a mutual-adjacency triple.
- `cubic_bridgeless` is used in Row 1/2/3 (the header says Row 2 only — actually applied uniformly).
