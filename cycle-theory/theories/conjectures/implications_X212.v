(** * Cycle.conjectures.implications_X212 — wave X212 dependency-graph EDGES

    Machine-checked edges between the eight Bondy–Murty rows of [X212.v] and the
    cycle-theory statements they relate to.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (cross-corpus consistency, [Qed]-closed)
    ════════════════════════════════════════════════════════════════════════════

      smith_two_longest_cycles_statement  ⟺  smith_longest_cycles_r_connected_statement

    Smith's conjecture on longest cycles enters the corpus twice: as the
    Bondy–Murty row [bm:bm-064] (authored here, [X212.v]) and as the studies
    slice [studies:std_smith_s_conjecture_longest_cycles_in_r_connected]
    (already committed as [X10.smith_longest_cycles_r_connected_statement]).
    The two independently written Rocq bodies are proved EQUIVALENT below.  This
    is the cross-check of point 6 of the faithfulness protocol applied to a
    duplicated source: the encodings were produced from two different corpus
    texts, so their equivalence is evidence that both are faithful, and a
    failure would have flagged one of them.  The proof is a pure unfolding of
    the two "longest cycle" predicates — [X10]'s conjunction
    [ucycle /\ 2 < size /\ maximality] versus [X212]'s boolean
    [ucycleb && 2 < size] plus maximality — and resolves neither endpoint.

    ────────────────────────────────────────────────────────────────────────────
    AUDITED NON-EDGES (candidates, machine-readable)
    ────────────────────────────────────────────────────────────────────────────

    The three confirmed corpus relations e209, e218 and e246 whose two endpoints
    are now both formalized do NOT close under the committed formulations; each
    is recorded below as a [candidate] with the precise obstruction.  None of
    them is a doubt about the mathematics: they are hypothesis-class or
    member-shape mismatches, plus in one case a genuine missing theorem. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6 X10 X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** The two "longest cycle" encodings agree *)

Lemma x212_longest_cycleE (G : sgraph) (c : seq G) :
  x212_longest_cycle c <-> x10_longest_cycle c.
Proof.
rewrite /x212_longest_cycle /x10_longest_cycle /x212_cycle; split.
- case=> /andP[uc sc] mx; split; first exact: uc.
  split; first exact: sc.
  by move=> c' uc' sc'; apply: mx; apply/andP; split; [exact: uc' | exact: sc'].
- case=> uc [sc mx]; split; first by apply/andP; split; [exact: uc | exact: sc].
  by move=> c' /andP[uc' sc']; apply: mx.
Qed.

(** ================================================================= *)
(** ** The scheduled edge *)

(*@EDGE from=smith_two_longest_cycles_statement to=smith_longest_cycles_r_connected_statement kind=equiv status=verified-literature proved=true proof=smith_two_longest_cycles_equiv_smith_longest_cycles_r_connected cite="Smith's conjecture on longest cycles, Bondy-Murty Appendix A #64 (bm:bm-064) and the studies slice studies:std_smith_s_conjecture_longest_cycles_in_r_connected (X10.v); see Grotschel 1984" note="Same conjecture recorded twice in the corpus; the two independently written Rocq bodies differ only in the presentation of the longest-cycle predicate (X10: ucycle /\\ 2 < size /\\ maximality; X212: the boolean ucycleb && 2 < size plus maximality) and are proved equivalent by unfolding" *)
Theorem smith_two_longest_cycles_equiv_smith_longest_cycles_r_connected :
  smith_two_longest_cycles_statement <-> smith_longest_cycles_r_connected_statement.
Proof.
split=> H k G c d hk hcon hc hd.
- exact: H hk hcon (proj2 (x212_longest_cycleE c) hc)
                   (proj2 (x212_longest_cycleE d) hd).
- exact: H hk hcon (proj1 (x212_longest_cycleE c) hc)
                   (proj1 (x212_longest_cycleE d) hd).
Qed.

(** ── Audited non-edges (machine-readable; extracted by build_edge_graph.py) ── *)

(*@EDGE from=small_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=candidate proved=false cite="gc:e209; Bondy 1990, small cycle double cover conjecture; its own corpus context says it strengthens the CDC conjecture" note="Does NOT compile under the committed formulations: bm-013 is restricted to SIMPLE multigraphs (simple_mgraph) while cycle_double_cover_statement (U6.v row 11) quantifies over ALL bridgeless multigraphs. The corpus argument closes the gap by the standard reduction of the CDC to the simple cubic case (suppress degree-2 vertices, split vertices, loops covered twice), which is real graph content and not a node-to-node reduction" *)

(*@EDGE from=orientable_five_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=candidate proved=false cite="gc:e218; Archdeacon 1984 / Jaeger 1985, orientable five cycle double cover conjecture" note="Does NOT compile under the committed formulations, for two independent reasons: (i) member shape, bm-026 yields five EVEN SUBGRAPHS while cdc (U6.v) demands single CIRCUITS, so the even-subgraph-to-circuit decomposition theorem is needed; (ii) hypothesis class, bm-026 assumes two_edge_connected (connected AND bridgeless) while cycle_double_cover_statement only assumes bridgeless, so disconnected bridgeless multigraphs are not covered" *)

(*@EDGE from=orientable_five_cycle_double_cover_statement to=five_flow_statement kind=implies status=candidate proved=false cite="gc:e246; Oum, A proof of the cycle double cover conjecture by OpenAI: an exposition, arXiv:2607.16356v3 Section 9.3 Conjecture 21 and Lemma 22; C.-Q. Zhang, Integer Flows and Cycle Covers of Graphs, Lemma 13.1.5" note="Does NOT compile under the committed formulations: the construction phi = sum_i i*chi_i mod 5 from the five signed characteristic vectors gives a nowhere-zero Z_5-flow, and turning that into a nowhere-zero INTEGER 5-flow is Tutte's Z_k-flow/k-flow theorem, which is not formalized here (the sibling edge e174 in implications_X228.v carries its circular-flow analogue as an explicit external hypothesis). The hypothesis classes also differ, two_edge_connected versus bridgeless, as in e218" *)

(** ** Axiom audit ********************************************************* *)

Print Assumptions x212_longest_cycleE.
Print Assumptions smith_two_longest_cycles_equiv_smith_longest_cycles_r_connected.
