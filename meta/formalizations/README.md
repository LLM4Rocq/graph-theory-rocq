# Checked graph-theory resolutions

Seven source records now have exact, assumption-free Rocq proofs in this repository. Six are new formalizations; Question 5.9 reuses an existing construction through a new statement bridge.

| Source record | Checked result | Final module |
|---|---|---|
| `2103.15175__00` | List Ramsey least forcing order `s^k+1`, for all `s>=2`, `k>=1` | [list_ramsey_graph.v](../../extremal-graph-theory/theories/applications/list_ramsey_graph.v) |
| `2408.02400__00` | For every `k>=5`, a graph with clique number 4, cochromatic number `k`, and chromatic number `k+3` | [cochromatic_gap.v](../../chromatic-theory/theories/applications/cochromatic_gap/cochromatic_gap.v) |
| `2512.10438__00` | Six-color, nine-vertex nontransitive tournament with longest avoiding path 7 vertices, below the exact transitive benchmark 8 | [color_avoiding_tournament.v](../../digraph-theory/theories/applications/color_avoiding_tournament.v) |
| `2310.04265__09` | Negation of the existing Question 5.9 statement | [question_5_9_resolution.v](../../digraph-theory/theories/applications/question_5_9_resolution.v) |
| `1812.02420__03` | No directed Kneser graph at `(k,b)=(5,3)`, refuting the universal existence statement | [directed_kneser_nonexistence.v](../../digraph-theory/theories/applications/directed_kneser_nonexistence.v) |
| `2209.09107__00` | The triangle refutes printed Alon–Tarsi Question 6.1 with its unfloored degree bound | [alon_tarsi_triangle.v](../../chromatic-theory/theories/applications/alon_tarsi_triangle.v) |
| `1611.03196__03` | Conjecture 1.15: every bipartite `G` with `Delta(G)>0` and any `m` edge sets `E_i` admit a matching of size at least `#E(G)/Delta(G) - c(m)` meeting each `E_i` in at most `ceil(#E_i/Delta(G))` edges, with `c(m) = (m+1)^2 (16m+29) <= 32(m+1)^3` | [fair_matching.v](../../packing-theory/theories/foundations/fair_matching.v) |

The last entry, added on 2026-09-16, is proved through Alon's Splitting Necklace
Theorem: König line colouring, then Carathéodory over the rationals, then an
interpolation of two matchings obtained by splitting the necklace of their
symmetric difference between two thieves, iterated along binary expansions, then
trimming. It follows the LLM attack recorded in
`packing-theory/theories/conjectures/X15.v` except on one point, stated in the
proof file: every interpolation is a halving, an arbitrary ratio being reached by
a chain of halvings, in place of the write-up's prescribed-ratio splitting lemma,
which does not follow from the equal-share necklace theorem at a cut cost
independent of the ratio. The same file also proves X15's own
`bipartite_matching_underrepresentation_llm_statement` with the constant
`32(m+1)^3` claimed by the attack, and
`bipartite_matching_underrepresentation_llm2_statement` with the sharper constant
above. The topological and classical inputs — Alon's theorem via Meunier's
simplotopal Tucker lemma, König's line colouring, Carathéodory over the
rationals, and the structure of the union of two matchings — are new in the
`classical-lemmas` package, which depends only on MathComp and GraphTheory and on
which `packing-theory` now depends; see
[X15_FAIR_MATCHING_REPORT.md](../../packing-theory/docs/X15_FAIR_MATCHING_REPORT.md)
and `classical-lemmas/NECKLACE_STATUS.md`. Unlike the six entries above, its
source correspondence has **not** been independently reviewed: the registry entry
names no reviewer. The statement it proves is the pre-existing, already-reviewed
encoding of Conjecture 1.15 in `X15.v`, unchanged.

## Checked repair artifacts

Two further Rocq developments repair finite proof steps without resolving their
source conjectures. The frozen-colouring modules prove `(n+4)F <= 4P` and
`P > 0` for connected noncomplete graphs with `Delta+1` colours; the
[frozen-colouring result](../../chromatic-theory/theories/applications/gap_repairs/frozen_coloring_resolution.v)
also identifies frozen proper colourings with those isolated under one-vertex
recolouring. The [six-cycle certificate](../../chromatic-theory/theories/applications/gap_repairs/viable_boundary.v)
proves the exact grid-map viability condition for both boundary hue labellings.

These artifacts are not entries in the resolution registry: the broader
dynamics and arbitrary-parameter planar-construction conclusions remain
unformalized. The [repair audit](../GAP_REPAIRS.md),
[development journal](../GAP_REPAIRS_JOURNAL.md), and
[assumption transcript](../GAP_REPAIR_ASSUMPTIONS.txt) record their scope and
verification.

From the repository root, using an installed compatible switch:

```sh
ROCQ_OPAM_SWITCH=rocq-tools make resolutions
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/test_formal_resolutions.py
ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs
make audit
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/formal_resolutions.py \
  --report meta/formalizations/ASSUMPTIONS.txt
```

The development environment used Rocq 9.1.1, OCaml 5.3.0 and the installed MathComp/GraphTheory libraries in `rocq-tools`. The live checker builds the required local dependencies and rejects nonclosed assumptions and mismatched statements. It preserves historical source statuses.

Read the [first-round development journal](JOURNAL.md) and [second-round journal](ROUND2_JOURNAL.md) for the proof attempts, MCP workflow, certificate optimizations and integration decisions. The [assumptions transcript](ASSUMPTIONS.txt) records the successful six-entry check. The [registry documentation](../FORMAL_RESOLUTIONS.md) explains source correspondence and the validation contract.

Validation on 2026-09-17: `python3 meta/check_milestone.py X15 packing-theory`
passed all 11 acceptance checks, which includes the live registry check for
`1611.03196__03` — the registered sources are recompiled and a fresh probe checks
`Check (theorem : statement)` and reports `Closed under the global context` for
both constants. The whole-registry run `make resolutions` cannot be completed in
the current switch for an unrelated reason: the `1812.02420__03` entry lives in
`digraph-theory`, which requires MathComp's `boolp`/`classical_sets`, absent
here.

Validation on 2026-09-05: all six resolutions passed, both new proof objects passed independent `rocqchk` validation, all 14 checker regression tests passed, and `make audit` passed. The native X2 milestone passed all 11 acceptance checks. The second round was developed in an isolated worktree based on the pushed first-round proof commit. The old dependency-graph drift belongs to the separate library-migration checkout. Source correspondence was independently reviewed by other agents and remains open to human mathematical review.
