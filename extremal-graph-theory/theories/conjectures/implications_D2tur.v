(** * Extremal.conjectures.implications_D2tur — relative implication/refutation
    edges among milestone D2tur's six open-problem nodes.

    Each edge, if scheduled, is a Qed-closed RELATIVE theorem
    [Theorem <A>_implies_<B> : A_statement -> B_statement] provable WITHOUT
    resolving either endpoint, and is restricted to the §6 verified-literature
    set (the Qed gate is the safeguard; a false edge must fail to compile).

    ── RESULT FOR D2tur: no verified-literature edge exists among these six nodes. ──

    D2tur's nodes are six mutually-independent open problems in extremal &
    structural graph theory, over heterogeneous carriers and logical shapes:

      (1) what_is_the_smallest_number_of_disjoint_spanning_tre_statement
            — over a complete WEIGHTED graph ([V : finType], [w : V->V->nat]):
              a greedy disjoint shortest-spanning-tree decomposition exists with
              a SMALLEST [k] whose union contains a Hamiltonian path
              (existence + minimality of a decomposition index).
      (2) turan_number_of_a_finite_family_statement
            — over a finite family [Fam : 'I_k -> sgraph]: some member [F0] has
              ex(n,F0) = O(ex(n,F)) (an eventual cross-multiplied edge-count bound).
      (3) good_edge_labelings_statement
            — over [sgraph]: for every c<4, finitely many good-edge-labeling
              CRITICAL graphs of average degree < c (a vertex-count bound).
      (4) sidorenkos_statement
            — over a PAIR [H G : sgraph] with [H] bipartite: a cross-multiplied
              homomorphism-count lower bound hom(H,G) >= (2|E(G)|/|V|^2)^|E(H)| |V|^|V(H)|.
      (5) number_of_cliques_in_minor_closed_classes_statement
            — over [sgraph]: a constant [c] with clique_count(G) <= c^t |V(G)|
              for every K_t-minor-free G (existence of one universal constant).
      (6) minimal_graphs_with_a_prescribed_number_of_spanning_statement
            — over [nat]: alpha(n) = o(log n), the least vertex count of a graph
              with exactly n spanning trees (an asymptotic, log-free density bound).

    The plan's §6 verified-literature edge table contains NO edge with any of
    these as an endpoint (its edges are chromatic/cycle/flow/directed:
    Petersen-colouring ⟹ Berge–Fulkerson / CDC, strong-k-CDC ⟹ CDC,
    circular-embedding ⟹ CDC, 4-flow ⟺ 3-edge-colouring).  No forbidden /
    withdrawn edge (Reed⟹B-K, list-total⟹Behzad, list-Hadwiger⟹Hadwiger,
    CH⟹Seymour-2nd-neighbourhood) touches D2tur either, so there is nothing to
    encode as a global negation.

    Why no genuine edge can be *re-derived* here (Qed-gate analysis):

    • The six rows range over DISJOINT carriers — a weighted complete finType
      graph (1), a finite [sgraph] family (2), a single [sgraph] (3) and (5), a
      bipartite [sgraph] pair (4), and the integers (6).  No row's conclusion is
      phrased over the object another row quantifies, so no entailment map exists.

    • None of the six is TRUE-by-theorem (unlike D5's MSS node): Sidorenko (4) is
      open in general, the Turán-family conjecture (2), good-edge-labeling
      finiteness (3), the c^t·n clique bound (5), the disjoint-spanning-tree
      question (1) and alpha(n)=o(log n) (6) are all open.  So there is no
      true-sink to which a vacuous hypothesis-discarding edge could point — and
      such a vacuous edge would be policy-forbidden in any case.

    • Every pair is simultaneously SATISFIABLE (the rows speak about unrelated
      objects), so no pair is contradictory: there is no refutation edge
      [A_statement -> ~ B_statement] either.

    • The three structurally-CLOSEST pairs still fail to connect, and are NOT
      forced (policy §6 / R4 — a candidate whose exact endpoints do not match is
      not scheduled).  They are recorded below as refuted-direction @EDGE
      annotations (documenting WHY each is a non-edge) so the federated extractor
      sees them rather than a silent gap:

        – (1) vs (6): both mention "spanning trees", but (1) is an
          existence+minimality claim over a weighted complete graph's greedy
          decomposition, while (6) is an asymptotic on the least vertex count
          realising a prescribed spanning-tree COUNT.  Neither reduces to the
          other; the shared word "spanning tree" is not shared structure.

        – (2) vs (5): both are extremal counts under a forbidden substructure,
          but (2) bounds the EDGE count of family-(subgraph)-free graphs while
          (5) bounds the CLIQUE count of K_t-MINOR-free graphs; the forbidden
          relation (subgraph vs minor) and the counted object (edges vs cliques)
          both differ, and neither bound entails the other.

        – (2) vs (4): both involve a graph's edge count, but (4) is a homomorphism
          lower bound for a bipartite H into an arbitrary G, while (2) is an
          upper-bound asymptotic on the extremal edge count; they share no
          common inequality, in either direction.

    Consequently this milestone schedules ZERO verified edges — there is no real
    [Theorem A_implies_B. Qed] to add.  The file imports the node statements only
    to confirm they are in scope and that this (edge-empty) module compiles
    axiom-free (no Conjecture/Axiom/Parameter/Admitted, no [Theorem … Qed]
    asserting an unproven or vacuously-forced edge). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph minor.
From GTBase Require Import base.
From Extremal.conjectures Require Import D2tur.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoints in scope (sanity): the six D2tur nodes are well-typed [Prop]s.
    No edge is provable among them; see the module header for the §6 / Qed-gate
    justification. *)
Check what_is_the_smallest_number_of_disjoint_spanning_tre_statement : Prop.
Check turan_number_of_a_finite_family_statement : Prop.
Check good_edge_labelings_statement : Prop.
Check sidorenkos_statement : Prop.
Check number_of_cliques_in_minor_closed_classes_statement : Prop.
Check minimal_graphs_with_a_prescribed_number_of_spanning_statement : Prop.

(** ** Edges.

    No verified-literature edge exists among the six D2tur nodes, so no
    [Theorem … Qed] is asserted here, and there is no literature-motivated
    candidate direction to record.  The machine-readable annotations below
    document the three structurally-closest pairs and WHY each is a non-edge, so
    the federated edge extractor records them as refuted-direction (not to be
    stated) rather than leaving a silent gap. *)

(*@EDGE from=what_is_the_smallest_number_of_disjoint_spanning_tre_statement to=minimal_graphs_with_a_prescribed_number_of_spanning_statement kind=implies status=refuted-direction proved=false cite="plan v4 §6 edge policy / R4; OPG: disjoint shortest spanning trees (open Question) and minimal graphs with a prescribed number of spanning trees (open Conjecture, alpha(n)=o(log n))" note="Non-edge. Both mention spanning trees but over disjoint carriers: (1) asserts existence + minimality of a greedy disjoint shortest-spanning-tree decomposition index k whose union contains a Hamiltonian path on a weighted complete finType graph; (6) is an asymptotic bound on the least vertex count realising a prescribed spanning-tree COUNT. Neither reduces to the other; the shared phrase is not shared structure. Not stated." *)

(*@EDGE from=turan_number_of_a_finite_family_statement to=number_of_cliques_in_minor_closed_classes_statement kind=implies status=refuted-direction proved=false cite="plan v4 §6 edge policy / R4; OPG: Turan number of a finite family (open Conjecture) and number of cliques in minor-closed classes (open Question)" note="Non-edge. Both are extremal counts under a forbidden substructure, but (2) bounds the EDGE count of family-(subgraph)-free n-vertex graphs while (5) bounds the CLIQUE count of K_t-MINOR-free graphs by c^t*|V|. The forbidden relation (subgraph vs minor) and the counted object (edges vs cliques) both differ; neither bound entails the other. Not stated." *)

(*@EDGE from=turan_number_of_a_finite_family_statement to=sidorenkos_statement kind=implies status=refuted-direction proved=false cite="plan v4 §6 edge policy / R4; OPG: Turan number of a finite family (open Conjecture) and Sidorenko's conjecture (open)" note="Non-edge. Both involve a graph's edge count, but (4) is a homomorphism-count LOWER bound for a bipartite H into an arbitrary G, while (2) is an asymptotic UPPER bound on the extremal edge count of family-free graphs. They share no common inequality in either direction. Not stated." *)
