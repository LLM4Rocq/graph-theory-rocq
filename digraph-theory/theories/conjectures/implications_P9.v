(** * Digraph.conjectures.implications_P9 — milestone P9 implication/refutation edges

    Machine-checked implication EDGES between the 20 P9 [_statement] nodes of
    [P9.v]. Following the convention of [implications.v]/[implications2.v], every
    scheduled edge would be a *relative* theorem [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving/refuting) either endpoint.

    POLICY (OPG_FULL_FORMALIZATION_PLAN.md §6): schedule a [Qed]-closed
    [Theorem A_implies_B] ONLY for edges whose status is *verified-literature*; a
    *candidate* edge must first be re-derived and is recorded as an annotation only
    (the Qed gate decides whether it is promoted); a *refuted-direction* edge is
    NEVER asserted as a global negation.

    RESULT OF THE AUDIT.  The 20 P9 nodes are mutually-independent open directed
    problems (the directed gap-closure milestone).  Plan §6 lists NO verified
    directed implication edges and states "Directed edges stay inside digraph-theory
    (its existing, already Qed-closed edges); do not assert new shaky CH⟹Seymour-type
    edges".  We re-examined the closest structural pairs and confirm that NONE close
    under their exact [P9.v] formulations:

      • Row 7 [partitioning_planar_digraphs_statement] vs
        Row 20 [large_acyclic_induced_subdigraph_in_a_planar_oriente_statement].
        These share IDENTICAL hypotheses (loopless oriented digraph whose underlying
        simple graph is [planar_sg]).  A 2-partition into two acyclic induced
        subdigraphs (Row 7) yields, by pigeonhole, an acyclic induced subdigraph of
        order ≥ ⌈|V|/2⌉ — but Row 20 demands order ≥ (3/5)|V| ([5·#S ≥ 3·#V]).  Since
        1/2 < 3/5 the implication does NOT close; it is a strict weakening, not an
        edge.  (Recorded as a candidate that FAILS the gate — never scheduled.)

      • Row 14 [decomposing_k_arc_strong_tournament_into_k_spanning_statement] vs
        Row 13 [arc_disjoint_out_branching_and_in_branching_statement].
        Row 14 gives, for a [k]-arc-strong TOURNAMENT, [k] arc-disjoint spanning
        strong subdigraphs; via Edmonds' branching theorem each strong spanning
        subdigraph carries an out-branching (and one carries an in-branching), so for
        k = 2 a tournament gets arc-disjoint out-/in-branchings.  But Row 13 is
        quantified over ALL [diGraphType] with a SINGLE existential [k]; Row 14 is
        tournament-only.  The formalized edge therefore cannot close (domain +
        quantifier mismatch); the bridge (Edmonds) is external/unformalised.

      • Row 18 [oriented_trees_in_n_chromatic_digraphs_statement] (Burr) vs
        Row 5 [antidirected_trees_in_digraphs_statement].  Although every
        [antidirected_tree] is an [oriented_tree], the two hypotheses are
        incomparable: Burr's is [2k−2 ≤ χ(underlying D)] while Row 5's is the
        arc-count [(k−2)·|V| < nb_arcs D].  Neither bridge holds — a dense graph can
        have χ = 2 (complete bipartite), and a high-χ graph can have few arcs (a
        small critical subgraph).  So there is NO implication in EITHER direction;
        this is a thematic relation only and is deliberately NOT recorded as an edge.

    Hence this file schedules ZERO verified [Qed] edges and carries only the two
    machine-readable candidate annotations below (proved=false).  Adding any of the
    above as a forced theorem would either fail to compile or smuggle in the
    conclusion as an "external" hypothesis — both are forbidden by §6.

    The file still [Require]s [P9] so the [from]/[to] endpoint names resolve and the
    annotations are checked against real constants. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core dichromatic packing colouring_variants two_extremal.
From Digraph Require Import interop_graph_theory chi_bounded.
From Digraph Require Import P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoint resolution check (each [from]/[to] below is a real P9 constant). *)
Check partitioning_planar_digraphs_statement : Prop.
Check large_acyclic_induced_subdigraph_in_a_planar_oriente_statement : Prop.
Check decomposing_k_arc_strong_tournament_into_k_spanning_statement : Prop.
Check arc_disjoint_out_branching_and_in_branching_statement : Prop.

(** ** Candidate edges (annotation-only; both FAIL the Qed gate as formalised).

    These are NOT scheduled as theorems: a candidate is promoted to a real
    [Theorem A_implies_B] only once it closes with [Qed], which neither does. *)

(*@EDGE from=partitioning_planar_digraphs_statement to=large_acyclic_induced_subdigraph_in_a_planar_oriente_statement kind=implies status=candidate proved=false cite="Neumann-Lara 1985 (2-dicolourability of planar digraphs) vs Albertson-Berman / Borodin-type 3/5 acyclic-set bound" note="Identical planar hypotheses; pigeonhole on a 2-acyclic-partition yields an acyclic induced subdigraph of order only >= |V|/2, strictly weaker than the required 3/5 (1/2 < 3/5), so the implication does not close. Strict weakening, not a valid edge." *)

(*@EDGE from=decomposing_k_arc_strong_tournament_into_k_spanning_statement to=arc_disjoint_out_branching_and_in_branching_statement kind=implies status=candidate proved=false cite="Bang-Jensen & Yeo, J. Graph Theory 2004 (k-arc-strong tournament decomposition); Edmonds 1973 (arc-disjoint branchings)" note="Row 14 (tournament, all k) gives k arc-disjoint spanning strong subdigraphs; with k=2 Edmonds' branching theorem extracts arc-disjoint out-/in-branchings. But Row 13 quantifies over ALL diGraphType with a single existential k, while Row 14 is tournament-only: domain+quantifier mismatch, and the Edmonds bridge is external/unformalised, so the edge cannot close as formalised." *)
