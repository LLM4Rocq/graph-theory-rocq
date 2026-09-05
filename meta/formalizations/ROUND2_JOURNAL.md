# Second formalization round — 2026-09-05

## Starting from the pushed proofs

The user reported pushing the first four formal resolutions and asked to proceed with further proofs. Local refs confirm `codex/formal-resolutions` and `origin/codex/formal-resolutions` both point to `80c33db`. The original directory remains on a dirty library-migration branch. Created a separate worktree, `graph-theory-rocq-next-proofs`, on `codex/formal-resolutions-next`, based on the proof commit.

An independent agent rebuilt the four existing resolutions from source in that worktree, without copying old compiled artifacts. All four exact-type and closed-assumption checks passed, as did all 14 proof-checker regression tests. `make audit` also passed; the previous dependency-graph drift belongs to the other, dirty migration checkout.

## Selecting the next results

Selected directed Kneser Problem 5.40 (`1812.02420__03`) and the printed Alon–Tarsi Question 6.1 (`2209.09107__00`). Both have finite obstructions and source definitions that can be expressed exactly in the available library. The Kneser row already has a formal statement in `Digraph.conjectures.X2`.

The heavy-path claim (`1904.12273__01`) needs a parametric graph family of order `3q+4`, with four outside major vertices; it is not a four-vertex graph. It has no existing formal statement, and requires definitions of shortest long odd holes and a uniform catching-path bound. The referee report's stronger candidate-graph assertion was supported by sampled computations, not a general candidacy proof. Deferred this result until that groundwork is explicit. Tree path-partition optimality and diamond-chain forward covers also require substantial new parametric graph and path infrastructure.

## Alon–Tarsi: meaning before computation

Read the [original Question 6.1](https://arxiv.org/html/2209.09107v2#S6), the attack, and the independent referee report. The source lower bound has no floor. The formal integer equivalent is `degree_G <= 2*outdegree+1`, preserving behavior at degree zero without truncated subtraction. The chosen arc set selects and orients a subset of the original graph edges on the same vertex carrier, so it is an orientation of a spanning subgraph.

The parity foundation defines even and odd Eulerian spanning subgraphs as arc subsets, including the empty set. Complementation in an odd-sized Eulerian arc set is an involution, preserves the Eulerian property, and reverses parity. This gives a fully proved bijection and equal parity counts. A separate symbolic grounding lemma verifies that the empty arc set is Alon–Tarsi. Both the generic obstruction and the empty case compile with closed assumptions and pass `rocqchk`.

The root agent used rocq-evolve for the triangle degree lemma and the correspondence between arbitrary triangle arc sets and nine Boolean entries. The MCP server retained load paths from the previous project, so self-contained scratch files supplied the same definitions for interactive development; final sources are compiled with their actual namespace. Direct exhaustive evaluation encountered locked MathComp cardinalities. The finite certificate is being normalized to explicit Boolean data, and no unfinished attempt will count as a proof.

## Directed Kneser: a structural finite contradiction

Read the source's digraph conventions: anti-parallel arcs are allowed and form a directed cycle of length two. The existing X2 statement permits arbitrary arc relations, but its singleton instances force looplessness. The proof specializes the universal claim to `k=5,b=3`. Pairwise intersection constraints rule out digons. Carefully chosen triples force arcs between each pair in a four-vertex configuration; their intersections forbid directed triangles, which forces acyclicity, contradicting the empty intersection of all four.

General helper lemmas and the exact finite subset facts are being compiled separately. The final theorem will negate the unchanged X2 statement directly. A separate agent reviews the source correspondence and registry integration.


## Completed proofs and integration

Both exact disproofs are complete. The Kneser proof establishes nonexistence at `(5,3)` and directly negates the unchanged X2 statement. Its 292-line source uses structural acyclicity arguments; only tiny subset cardinalities use `vm_compute`. Compilation against the clean proof branch took about 26 seconds. The full parameter classification in the attack is not claimed as formalized.

For Alon–Tarsi, the final method avoids VM evaluation entirely. Proved explicit formulas for quantification and cardinality on the three triangle vertices and nine ordered pairs. The orientation condition rules out diagonal arcs. Case analysis on the six remaining Boolean arc entries proves that any qualifying arc set is Eulerian and has odd cardinality. Applying the complement-parity theorem gives the contradiction. The application compiles in about two seconds. The earlier finite-set and nine-bit VM attempts remain unsuccessful scratch experiments; their results are not used by the final proof.

The reusable parity theorem is installed as `chromatic-theory/theories/foundations/alon_tarsi.v`. The final applications are `chromatic-theory/theories/applications/alon_tarsi_triangle.v` and `digraph-theory/theories/applications/directed_kneser_nonexistence.v`. The two package project files include these modules. No existing statement definition or pinned source status changed.

An independent agent reviewed the final definitions, each arbitrary-object completeness argument, and each source-statement bridge. The [resolution registry](../formal_resolutions.json) retains its original four entries and adds exactly two new entries, including the unchanged X2 declaration hash and the new Question 6.1 declaration hash. Agent source readback supplements the kernel check; human mathematical review can still assess the source interpretation.

All six resolutions passed the live checker in the new worktree, including recompilation, exact theorem types, and closed assumptions for both statements and proofs. The [assumptions transcript](ASSUMPTIONS.txt) now records all six.

The first post-integration `make audit` detected the new foundation missing from the generated module inventory. Regenerating `meta/CORPUS_STATUS.md` changed exactly one line, adding `alon_tarsi` to the chromatic foundation list. The existing catalog counts and statuses were unchanged.


## Verification results

The six-entry live resolution checker succeeded. Its report has twelve closed-context messages: six statements and their six exact proofs. Independent `rocqchk -silent` validation of both new final modules and their dependencies exited successfully. All 14 existing real-compiler regression tests passed; the checker implementation itself was unchanged this round.

After the one-line foundation-inventory refresh, `make audit` passed with six valid registry entries, all 46 dependency edges unchanged, and no corpus-status drift. A source scan found no admissions, axioms, aborted proofs or unchecked casts in the three new modules. The overview and journal links resolve, and `git diff --check` passed. The original four registry entries are structurally identical to the pushed baseline.

The original dirty migration checkout was not modified by this round. The reviewable changes are on `codex/formal-resolutions-next` in the `graph-theory-rocq-next-proofs` worktree.


The native X2 milestone also passed all 11 acceptance checks: its package compiled, all 11 source statements had closed assumptions, the registered Kneser disproof was verified, and the remaining 23 exact-type faithfulness probes were preserved. This completes validation of the second batch.
