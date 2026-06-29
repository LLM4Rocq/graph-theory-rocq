(** * Spectral.conjectures.implications_D5 — relative implication/refutation edges
    among milestone D5's five open-problem nodes.

    Each edge, if scheduled, is a Qed-closed RELATIVE theorem
    [Theorem <A>_implies_<B> : A_statement -> B_statement] provable WITHOUT
    resolving either endpoint, and is restricted to the §6 verified-literature
    set (the Qed gate is the safeguard; a false edge must fail to compile).

    ── RESULT FOR D5: no verified-literature edge exists among these five nodes. ──

    D5's nodes are five mutually independent problems in spectral / algebraic
    graph theory, over heterogeneous carriers and logical shapes:

      (1) triangle_free_strongly_regular_graphs_statement
            — EXISTENCE of 8 pairwise non-isomorphic triangle-free SRGs
              (combinatorial: nat parameters k, lam, mu; no matrices).
      (2) signing_a_graph_to_have_small_magnitude_eigenvalues_statement
            — a UNIVERSAL claim (Marcus–Spielman–Srivastava 2015, a theorem):
              every d-regular graph admits a symmetric signing with spectral
              radius <= 2*sqrt(d-1).
      (3) are_almost_all_graphs_determined_by_their_spectrum_statement
            — an ASYMPTOTIC density limit over labelled n-graphs.
      (4) does_the_symmetric_chromatic_function_distinguish_tr_statement
            — EXISTENCE of two non-isomorphic trees with equal Stanley CSF
              (a colouring generating function, NOT eigenvalues).
      (5) laplacian_degrees_of_a_graph_statement
            — a UNIVERSAL majorisation c_k(G) >= d_k(G) for connected graphs.

    The plan's §6 verified-literature edge table contains NO edge with any of
    these as an endpoint (its edges are chromatic/cycle/flow/directed:
    Petersen-colouring, Berge–Fulkerson, CDC, 4-flow⟺3-edge-colouring). No
    forbidden/withdrawn edge (Reed⟹B-K, list-total⟹Behzad, list-Hadwiger⟹
    Hadwiger, CH⟹Seymour) touches D5 either.

    Why no genuine edge can be *re-derived* here (Qed-gate analysis):

    • Truth-value shortcuts are unavailable. (2) is the only true-by-theorem
      node, but A -> (2) needs a proof of (2) (= the MSS theorem), and a node
      cannot be proved false to make (¬node) -> B, so no trivial edge arises.

    • The two existential nodes (1) and (4) cannot feed one another or any
      universal node: there is no map turning 8 triangle-free SRGs into two
      cospectral-CSF trees, nor conversely, and an existence statement does not
      entail a "for all graphs" statement.

    • The two universal nodes (2), (3), (5) share no logical structure: a signing
      bound, an asymptotic spectral-determination density, and a Laplacian-vs-
      degree majorisation are independent in both directions.

    • The nearest *literature* link — non-isomorphic SRGs with equal parameters
      are cospectral mates — does NOT yield an edge between any two D5 endpoints:
      node (1) asserts existence of an 8th triangle-free SRG, which says nothing
      about whether that graph has a cospectral mate; and node (3) is an
      ASYMPTOTIC "almost all" density that finitely many cospectral families do
      not refute. So even the candidate "SRG cospectrality ⟹ spectral-
      determination" intuition fails to connect (1) to (3)'s exact formulation;
      we therefore do NOT force it (a candidate whose exact endpoints do not
      match is not scheduled — policy §6 / R4).

    Consequently this file schedules ZERO edges (no [_implies_]/[_equiv_]
    theorems), and emits no [(*@EDGE …*)] annotations: there is no edge — verified,
    candidate, or refuted-direction — whose endpoints are two distinct D5 nodes.
    The file imports the node statements only to confirm they are in scope and
    that this (edge-empty) module compiles axiom-free. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.
From Spectral Require Import conjectures.D5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sanity: all five D5 nodes are in scope as [Prop]s (no edge is provable
    among them; see the module header for the §6 / Qed-gate justification). *)
Remark D5_nodes_in_scope :
  (triangle_free_strongly_regular_graphs_statement : Prop) = triangle_free_strongly_regular_graphs_statement /\
  (signing_a_graph_to_have_small_magnitude_eigenvalues_statement : Prop) = signing_a_graph_to_have_small_magnitude_eigenvalues_statement /\
  (are_almost_all_graphs_determined_by_their_spectrum_statement : Prop) = are_almost_all_graphs_determined_by_their_spectrum_statement /\
  (does_the_symmetric_chromatic_function_distinguish_tr_statement : Prop) = does_the_symmetric_chromatic_function_distinguish_tr_statement /\
  (laplacian_degrees_of_a_graph_statement : Prop) = laplacian_degrees_of_a_graph_statement.
Proof. do 4 (split; [reflexivity|]); reflexivity. Qed.
