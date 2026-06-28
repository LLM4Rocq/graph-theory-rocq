(** * GTMisc.conjectures.implications_D7 — milestone D7 (misc) edges

    Implication / refutation EDGES among the five D7 "algorithmic & complexity"
    nodes:
      - Row 1 [algorithm_for_graph_homomorphisms_statement]
              (existence of an O(c^(|G|+|H|)) graph-homomorphism algorithm);
      - Row 2 [approximation_ratio_for_maximum_edge_disjoint_paths_statement]
              (MaxEDP in planar graphs: a sub-sqrt(n) approximation OR a
               stronger-than-APX inapproximability);
      - Row 3 [complexity_of_the_h_factor_statement]
              (NP-hardness of the fixed-H, fixed-c H-factor problem);
      - Row 4 [ptas_for_feedback_arc_set_in_tournaments_statement]
              (SOLVED: a PTAS for feedback arc set in tournaments);
      - Row 5 [finding_k_edge_outerplanar_graph_embeddings_statement]
              (poly-time computation of a minimal k-edge-outerplanar embedding),
    as Qed-closed RELATIVE theorems where one genuinely exists.

    OUTCOME (honest).  These five rows are MUTUALLY-INDEPENDENT algorithmic and
    complexity problems, grouped only by the "miscellaneous algorithmic" bucket.
    They range over disjoint carriers (a PAIR of [sgraph]s; a planar [edp_input];
    the abstract decision [problem] over min-degree graphs; a [t_input]
    tournament; a single [sgraph]) and disjoint subject matter (homomorphism
    existence, edge-disjoint path routing, vertex-disjoint H-covers, tournament
    feedback arc sets, outerplanar edge-layerings).  They share no common
    structural object on which a logical entailment could be built, and the
    verified-literature edge table of OPG_FULL_FORMALIZATION_PLAN.md §6 lists
    NONE of them.  Consequently this milestone schedules ZERO verified edges —
    there is no real [Theorem A_implies_B. Qed] to add, and per the edge policy a
    false/unclosing edge must NOT be forced (it must simply fail to compile).

    Why the obvious "shortcut" edges are NOT real edges (and are not asserted):

    • Row 4 is SOLVED, hence (in the literature) TRUE.  One could in principle
      construct an exact-optimum algorithm and prove
      [ptas_for_feedback_arc_set_in_tournaments_statement] OUTRIGHT, after which
      "[X_statement -> Row4_statement]" would type-check for EVERY [X] by
      discarding the hypothesis.  That is a VACUOUS edge — it expresses no
      entailment between the two problems and is exactly the kind of forced /
      non-edge the policy forbids.  We therefore do NOT assert any
      [_implies_ptas_for_feedback_arc_set_in_tournaments_statement] theorem.

    • No pair is CONTRADICTORY, so there is no refutation edge
      ([A_statement -> ~ B_statement]) either: all five Props are simultaneously
      satisfiable (they speak about unrelated objects), so none refutes another.

    • There is no literature-MOTIVATED candidate direction among the five
      (unlike U13's shuffle-exchange/Beneš pair, which are literally the same
      network family).  The two planar rows (Row 2 MaxEDP, Row 5
      k-edge-outerplanar embeddings) share only the ambient hypothesis
      [wagner_planar]; neither problem reduces to or specialises the other.  So
      we record no candidate annotation here.

    The file is self-contained: it [Require Import]s the node definitions from
    [GTMisc.conjectures.D7] so the edge endpoints are in scope, re-checks that
    all five are well-typed [Prop]s, and is axiom-free — no
    Conjecture/Axiom/Parameter/Admitted, and no [Theorem … Qed] asserting an
    unproven (or vacuously-forced) edge. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoints in scope (sanity): the five D7 nodes are well-typed Props. *)
Check algorithm_for_graph_homomorphisms_statement : Prop.
Check approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop.
Check complexity_of_the_h_factor_statement : Prop.
Check ptas_for_feedback_arc_set_in_tournaments_statement : Prop.
Check finding_k_edge_outerplanar_graph_embeddings_statement : Prop.

(** ** Edges.

    No verified-literature edge exists among the five D7 (misc algorithmic)
    nodes, so no [Theorem … Qed] is asserted here, and there is no
    literature-motivated candidate direction to record.  The machine-readable
    annotations below document the two structurally-closest pairs and WHY each
    is a non-edge, so the federated edge extractor records them as
    refuted-direction (not to be stated) rather than leaving a silent gap. *)

(*@EDGE from=ptas_for_feedback_arc_set_in_tournaments_statement to=algorithm_for_graph_homomorphisms_statement kind=implies status=refuted-direction proved=false cite="Kenyon-Mathieu-Schudy 2007 (FAS-tournaments PTAS); plan v4 §6 edge policy" note="Non-edge. Row 4 is SOLVED hence literature-true, but a true sink does NOT entail a different open problem; any X->Row4 would be a vacuous hypothesis-discarding edge and is policy-forbidden. The reverse (Row4->Row1) likewise has no logical content: tournament feedback arc sets and graph-homomorphism existence share no object. Not stated." *)

(*@EDGE from=approximation_ratio_for_maximum_edge_disjoint_paths_statement to=finding_k_edge_outerplanar_graph_embeddings_statement kind=implies status=refuted-direction proved=false cite="plan v4 §6 edge policy; Chuzhoy-Kim-Li 2016 (MaxEDP planar); Bienstock-Monma 1988 (outerplanarity computation)" note="Non-edge. The two planar rows share only the ambient hypothesis wagner_planar; a poly-time o(sqrt n)-approximation (or inapproximability) for MaxEDP gives no algorithm for computing a minimal k-edge-outerplanar embedding, and vice versa. No specialisation/reduction holds in either direction. Not stated." *)
