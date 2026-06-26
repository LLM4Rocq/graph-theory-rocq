(** * Chromatic.conjectures.implications_U8 — milestone U8 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the three committed U8
    conjecture statements (see [U8.v]).  As in the sibling [implications_U1.v] /
    [implications_U4.v] / [implications_U5.v] layers, every SCHEDULED edge is a
    *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving or refuting) either endpoint.  This file
    is axiom-free: no [Conjecture]/[Axiom]/[Parameter]/[Admitted]; bridge facts
    that would need resolving a conjecture are carried as EXPLICIT hypotheses,
    never asserted.

    The three U8 nodes are:
      • [bounding_the_chromatic_number_of_triangle_free_graph_statement]   (Row 1)
      • [graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement]   (Row 2)
      • [vertex_minor_closed_classes_are_chi_bounded_statement]            (Row 3)

    ════════════════════════════════════════════════════════════════════════════
    RESULT:  no verified-literature edge is internal to U8.
    ════════════════════════════════════════════════════════════════════════════

    The §6 verified-literature edge table (OPG_FULL_FORMALIZATION_PLAN) lists ONLY
    cycle / edge-colouring edges; none of its endpoints is a U8 node.  The single
    §6 *candidate* edge that touches U8 is

        vertex-minor-closed-χ-bounded  ⟹  forbidden-induced-tree-χ-bounded
        ( Row 3  ⟹  Row 2 ),

    and the [Qed] gate REFUTES it under the exact [U8.v] formulations.  It is
    therefore recorded as a candidate annotation (proved=false), NOT scheduled.

    ────────────────────────────────────────────────────────────────────────────
    Why Row 3 ⟹ Row 2 does NOT close (the obstruction is a missing closure law).
    ────────────────────────────────────────────────────────────────────────────

    To derive Row 2 from Row 3 one would, for a fixed tree [T], instantiate Row 3
    at the class  [F_T := fun G => ~ has_induced T G]  and discharge its two
    hypotheses:
      • [proper_class F_T] — easy: [T] itself satisfies [has_induced T T] (via the
        identity iso [T ≃ induced [set: T]]), so [~ F_T T], hence [F_T] is proper.
      • [vminor_closed F_T] — i.e. for all [G H], [F_T G] -> [vertex_minor H G] ->
        [F_T H]: if [G] has no induced [T] then NO vertex-minor of [G] does either.
        This is FALSE.  A vertex-minor is built from LOCAL COMPLEMENTATIONS
        ([local_complement]) and vertex deletions; local complementation toggles
        adjacency among a vertex's neighbours and can CREATE an induced [T] that
        the original [G] did not contain.  Forbidden-INDUCED-subgraph classes are
        closed under induced subgraphs and isomorphism, but NOT under local
        complementation — so [F_T] is, in general, not vertex-minor-closed and
        Row 3 simply does not apply to it.

    There is hence no purely logical derivation of Row 2 from Row 3 (one would
    need the false closure law as a bridge, which we will not assert).  The deep
    genuine relationship between Geelen's vertex-minor question (Row 3) and the
    Gyárfás–Sumner-for-trees conjecture (Row 2) is via rank-width / χ-boundedness
    of circle-graph-like classes, not an elementary relative implication.

    Citation.  J. Geelen, O. Kwon, R. McCarty, P. Wollan, "The grid theorem for
    vertex-minors", J. Combin. Theory Ser. B 158 (2023) 93–116 (vertex-minor
    closure / local complementation); A. Gyárfás, "Problems from the world
    surrounding perfect graphs", Zastos. Mat. 19 (1987) 413–441 and D. P. Sumner
    (forbidden-induced-tree χ-boundedness).  Status: candidate (§6); the Qed gate
    rejects the direct edge under the faithful [U8.v] statements.

    ────────────────────────────────────────────────────────────────────────────
    The other node pairs carry no textbook implication.
    ────────────────────────────────────────────────────────────────────────────

    • Row 1 (triangle-free degree bound χ ≤ ⌈Δ/2⌉+2) asserts a NUMERIC bound for a
      single structural class; Rows 2/3 assert χ-BOUNDEDNESS (existence of a
      bounding function in ω) of OTHER classes.  Row 1 neither implies nor is
      implied by a χ-boundedness statement: its conclusion is a fixed function of
      Δ on triangle-free graphs (where ω ≤ 2), unrelated to the ω-indexed bounding
      function of [chi_bounded], and its hypothesis (triangle-freeness) is not the
      hypothesis of Row 2 (forbidden induced tree) or Row 3 (proper vertex-minor
      closed).  No edge.

    • Row 2 ⟹ Row 3 is also not viable: Row 2 only bounds the specific
      forbidden-induced-tree classes, a family unrelated to "ALL proper
      vertex-minor-closed classes" of Row 3 (e.g. a proper vertex-minor-closed
      class need contain no forbidden induced tree at all).  No edge.

    Hence ZERO U8-internal verified-literature edges; the lone candidate is
    annotated below for the extractor and deliberately left unscheduled. *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    Each [from]/[to] is the exact [_statement] Definition name from [U8.v]. *)

(*@EDGE from=vertex_minor_closed_classes_are_chi_bounded_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=implies status=candidate proved=false cite="OPG_FULL_FORMALIZATION_PLAN §6 (vertex-minor-closed-chi-bounded => forbidden-induced-tree-chi-bounded); Geelen-Kwon-McCarty-Wollan, JCTB 158 (2023) 93-116; Gyarfas-Sumner" note="Refuted by the Qed gate under the faithful U8.v statements: deriving Row2 from Row3 needs vminor_closed (fun G => ~ has_induced T G), but forbidden-INDUCED-subgraph classes are NOT closed under local complementation, so Row 3 does not apply. Deep relationship is via rank-width, not an elementary relative implication." *)
