(** * Extremal.conjectures.implications_D2pr — relative implication/refutation
    edges among milestone D2pr's seven open-problem nodes.

    Each *scheduled* edge is a Qed-closed RELATIVE theorem
    [Theorem <A>_implies_<B> : A_statement -> B_statement] provable WITHOUT
    resolving either endpoint, restricted to the plan §6 verified-literature set
    (the Qed gate is the safeguard; a false edge must fail to compile, and a
    candidate whose exact endpoints do not match is NOT forced — policy §6 / R4).

    ── RESULT FOR D2pr: ZERO edges (verified, candidate, or refuted). ──

    D2pr's seven nodes are mutually independent problems in PROBABILISTIC /
    asymptotic graph theory, over heterogeneous carriers and logical shapes:

      (1) almost_all_non_hamiltonian_3_regular_graphs_are_1_co_statement
            [labelled edge sets {set {set 'I_(2n)}}; counts NH, NHB]
            — eventual ratio NHB(n)/NH(n) -> 1 (cross-multiplied ε–N).
      (2) coloring_random_subgraphs_statement
            [sgraph G; exact rational expectation Echi G over edge-subsets]
            — ∃ constant c > 0 with E[χ(G_{1/2})] > c·χ(G)/log χ(G) for all G.
      (3) shannon_capacity_of_the_seven_cycle_statement
            [strong powers of cycle_graph 7 over a realFieldType]
            — over every ordered field the Shannon capacity of C_7 is
              well-defined (inf-characterisation), 1 <= c.
      (4) negative_association_in_uniform_forests_statement
            [sgraph G with DISTINCT edges e ≠ f; counts of acyclic edge-sets]
            — cross-multiplied counting inequality for uniform random forests.
      (5) chromatic_number_of_random_lifts_of_complete_graphs_statement
            [lift parameters {ffun 'I_5*'I_5 -> {perm 'I_h}}; chiLift]
            — whp concentration of χ of a random lift of K_5 on one value.
      (6) random_stable_roommates_statement
            [preference profiles {ffun 'I_n -> {perm 'I_n}}; Pstar n]
            — solvability probability is Θ(n^{-1/4}) (root-free, via 4th powers).
      (7) asymptotic_distribution_of_form_of_polyhedra_statement
            [labelled 3-connected graphs on 'I_v; counts cP, Dk, Bk]
            — a limiting CDF F of β = v/(k+2) exists (eventual empirical
              convergence).

    §6 verified-literature edge table: contains NO edge with any D2pr node as an
    endpoint (its edges are chromatic/cycle/flow/directed: Petersen-colouring,
    Berge–Fulkerson, Cycle Double Cover, 4-flow<=>3-edge-colouring). No
    forbidden/withdrawn edge (Reed=>B-K, list-total=>Behzad, list-Hadwiger=>
    Hadwiger, Caccetta–Häggkvist=>Seymour-2nd-nbhd) touches D2pr either. So no
    edge is *scheduled* (no [_implies_]/[_equiv_] Theorem is closed here).

    ── Why no genuine edge can be re-derived (Qed-gate analysis). ──

    The seven nodes share neither carrier nor logical shape, and the literature
    treats them as seven separate open questions; there is no textbook reduction
    turning one into another (contrast D2ram, where multicolour Erdős–Hajnal is
    the literal Ramsey-coloured generalisation of Erdős–Hajnal — a real, if
    blocked, link).  Concretely:

    • Distinct objects, no shared quantification.  (1) counts labelled 3-regular
      edge sets; (2) is an expectation over random edge-subsets of an arbitrary
      G; (3) is a well-definedness target for one fixed graph C_7 over every
      ordered field; (4) is a counting inequality for forests of an arbitrary G;
      (5) is a concentration claim for random lifts of K_5; (6) is an asymptotic
      Θ for stable-roommates solvability; (7) is the existence of a limiting CDF
      for polyhedral β.  No map sends an outcome of one problem to an outcome of
      another, so no hypothesis-only derivation exists.

    • Truth-value shortcuts are unavailable.  None of the seven is provable
      outright here (all are OPEN, the very point of the milestone), so no
      A -> B arises from B being a theorem; and a node may not be proved false to
      manufacture (¬node) -> B.  Hence no trivial edge.

    • Asymptotic vs. exact, existential vs. universal.  (1),(5),(6),(7) are
      eventual/asymptotic; (2),(3),(4) are exact (a universal inequality, a
      well-definedness, a counting inequality).  An asymptotic statement does not
      entail an exact-for-all-G one, and the exact nodes (different carriers,
      different combinatorial content) do not entail each other's asymptotics.

    • The nearest superficial pairings still fail the exact-endpoints test, so
      per policy §6 / R4 we do NOT force them — they are not even candidates:
        – (2) χ of random subgraphs and (5) χ of random lifts both mention a
          chromatic number, but over disjoint sample spaces (edge-subsets of an
          arbitrary G vs. permutation lifts of the fixed K_5) and disjoint
          conclusions (an expectation lower bound vs. one-point concentration);
          neither statement's truth bears on the other's.
        – (1) almost-all-3-regular-non-Ham-are-connected and (7) limiting
          β-distribution are both labelled-graph asymptotics, but over different
          ensembles (3-regular edge sets vs. 3-connected graphs by edge count)
          and different targets (a ratio→1 vs. a full limiting CDF); one says
          nothing about the other.

    Consequently this file schedules ZERO edges (no [_implies_]/[_equiv_]
    theorems) and emits no machine-readable @EDGE annotations: there is no edge —
    verified, candidate, or refuted-direction — whose endpoints are two distinct
    D2pr nodes.  The file imports the node statements only to confirm they are in
    scope and that this (edge-empty) module compiles axiom-free. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Extremal Require Import conjectures.D2pr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sanity: all seven D2pr nodes are in scope as [Prop]s.  No [_implies_]/
    [_equiv_] Theorem is scheduled (see the module header for the §6 / Qed-gate
    justification that no edge — verified, candidate, or refuted — exists). *)
Remark D2pr_nodes_in_scope :
  (almost_all_non_hamiltonian_3_regular_graphs_are_1_co_statement : Prop)
    = almost_all_non_hamiltonian_3_regular_graphs_are_1_co_statement /\
  (coloring_random_subgraphs_statement : Prop)
    = coloring_random_subgraphs_statement /\
  (shannon_capacity_of_the_seven_cycle_statement : Prop)
    = shannon_capacity_of_the_seven_cycle_statement /\
  (negative_association_in_uniform_forests_statement : Prop)
    = negative_association_in_uniform_forests_statement /\
  (chromatic_number_of_random_lifts_of_complete_graphs_statement : Prop)
    = chromatic_number_of_random_lifts_of_complete_graphs_statement /\
  (random_stable_roommates_statement : Prop)
    = random_stable_roommates_statement /\
  (asymptotic_distribution_of_form_of_polyhedra_statement : Prop)
    = asymptotic_distribution_of_form_of_polyhedra_statement.
Proof. do 6 (split; [reflexivity|]); reflexivity. Qed.
