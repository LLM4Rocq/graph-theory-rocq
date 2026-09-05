# Checked graph-theory resolutions

Six source records now have exact, assumption-free Rocq proofs in this repository. Five are new formalizations; Question 5.9 reuses an existing construction through a new statement bridge.

| Source record | Checked result | Final module |
|---|---|---|
| `2103.15175__00` | List Ramsey least forcing order `s^k+1`, for all `s>=2`, `k>=1` | [list_ramsey_graph.v](../../extremal-graph-theory/theories/applications/list_ramsey_graph.v) |
| `2408.02400__00` | For every `k>=5`, a graph with clique number 4, cochromatic number `k`, and chromatic number `k+3` | [cochromatic_gap.v](../../chromatic-theory/theories/applications/cochromatic_gap/cochromatic_gap.v) |
| `2512.10438__00` | Six-color, nine-vertex nontransitive tournament with longest avoiding path 7 vertices, below the exact transitive benchmark 8 | [color_avoiding_tournament.v](../../digraph-theory/theories/applications/color_avoiding_tournament.v) |
| `2310.04265__09` | Negation of the existing Question 5.9 statement | [question_5_9_resolution.v](../../digraph-theory/theories/applications/question_5_9_resolution.v) |
| `1812.02420__03` | No directed Kneser graph at `(k,b)=(5,3)`, refuting the universal existence statement | [directed_kneser_nonexistence.v](../../digraph-theory/theories/applications/directed_kneser_nonexistence.v) |
| `2209.09107__00` | The triangle refutes printed Alon–Tarsi Question 6.1 with its unfloored degree bound | [alon_tarsi_triangle.v](../../chromatic-theory/theories/applications/alon_tarsi_triangle.v) |

From the repository root, using an installed compatible switch:

```sh
ROCQ_OPAM_SWITCH=rocq-tools make resolutions
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/test_formal_resolutions.py
make audit
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/formal_resolutions.py \
  --report meta/formalizations/ASSUMPTIONS.txt
```

The development environment used Rocq 9.1.1, OCaml 5.3.0 and the installed MathComp/GraphTheory libraries in `rocq-tools`. The live checker builds the required local dependencies and rejects nonclosed assumptions and mismatched statements. It preserves historical source statuses.

Read the [first-round development journal](JOURNAL.md) and [second-round journal](ROUND2_JOURNAL.md) for the proof attempts, MCP workflow, certificate optimizations and integration decisions. The [assumptions transcript](ASSUMPTIONS.txt) records the successful six-entry check. The [registry documentation](../FORMAL_RESOLUTIONS.md) explains source correspondence and the validation contract.

Validation on 2026-09-05: all six resolutions passed, both new proof objects passed independent `rocqchk` validation, all 14 checker regression tests passed, and `make audit` passed. The native X2 milestone passed all 11 acceptance checks. The second round was developed in an isolated worktree based on the pushed first-round proof commit. The old dependency-graph drift belongs to the separate library-migration checkout. Source correspondence was independently reviewed by other agents and remains open to human mathematical review.
