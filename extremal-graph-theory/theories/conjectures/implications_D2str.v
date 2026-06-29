(** * Extremal.conjectures.implications_D2str — milestone D2str EDGES

    Implication / refutation EDGES among the five D2str nodes (see [D2str.v]):

      Row 1  linear_hypergraphs_with_dimension_3_statement
             (a linear hypergraph of incidence-poset dimension ≤ 3 is the
              intersection hypergraph of triangles + segments in the plane);
      Row 2  geodesic_cycles_and_tuttes_theorem_statement
             (every 3-connected G admits an edge-length ℓ s.t. every ℓ-geodesic
              cycle is peripheral);
      Row 3  nearly_spanning_regular_subgraphs_statement
             (∀ε,k: large-r-regular G has a k-regular subgraph on ≥(1−ε)|V|);
      Row 4  simultaneous_partition_of_hypergraphs_statement
             (two r-uniform H₁,H₂ have one r-partition rainbow-rich for both);
      Row 5  covering_powers_of_cycles_with_equivalence_subgraphs_statement
             (the equivalence covering number of C_n^k is Ω(k)),

    as Qed-closed RELATIVE theorems where one genuinely exists.

    ────────────────────────────────────────────────────────────────────────
    AUDIT RESULT (honest): NO verified-literature edge among the five D2str
    nodes.  This milestone schedules ZERO verified edges.
    ────────────────────────────────────────────────────────────────────────

    The five rows are a deliberately diverse "deferred / structural" slice of
    the OPG corpus, grouped only by the D2str bucket.  They live over DISJOINT
    carriers and speak about DISJOINT subject matter:

      Row 1  T:finType + E:{set {set T}}  — incidence-poset dimension &
             plane (R*R) geometric representation of a LINEAR hypergraph;
      Row 2  G:sgraph + ℓ:G→G→R           — real edge metric, k-connectivity,
             geodesic/peripheral CYCLES;
      Row 3  G:sgraph + S:{set G},adj:rel G — REGULAR (degree-uniform)
             subgraphs of large-degree regular graphs;
      Row 4  T:finType + E1,E2:{set {set T}} + part:T→'I_r — simultaneous
             BALANCED r-PARTITION (rainbow density) of two r-uniform families;
      Row 5  graph_power (cycle_graph n) k — EQUIVALENCE-relation COVERS of a
             cycle-power graph.

    No pair carries a clean relative implication provable without resolving an
    endpoint, and the verified-literature edge table of
    OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of these problems.  Hence there
    is no real [Theorem A_implies_B. Qed] to add, and per the edge policy a
    false / non-closing edge must NOT be forced — it must simply fail to
    compile.

    Why the structurally-closest pairs are NOT edges (and are not asserted):

    • Row 1 vs Row 4 — the ONLY two nodes that share a carrier shape
      (T:finType with a hyperedge family {set {set T}}).  They are nonetheless
      INDEPENDENT.  Row 1 hypothesises a LINEAR hypergraph of incidence-poset
      dimension ≤ 3 and concludes a PLANAR geometric (triangle/segment)
      representation; Row 4 hypothesises TWO r-UNIFORM families and concludes a
      single r-partition that is simultaneously rainbow-dense for both.  Neither
      hypothesis class contains the other (a dimension-3 linear hypergraph need
      not be uniform, and a pair of r-uniform families need not be linear nor
      dimension-bounded), and neither conclusion transports to the other
      (a plane representation says nothing about a balanced partition, and a
      balanced partition gives no triangles/segments).  No direction reduces or
      specialises — refuted-direction, not stated.

    • Row 2 vs Row 5 — the two nodes that both mention CYCLES.  They are
      INDEPENDENT.  Row 2 is a Tutte-type metric existence statement about
      geodesic/peripheral cycles in an arbitrary 3-connected graph; Row 5 is an
      Ω(k) lower bound on the equivalence covering number of the SPECIFIC family
      C_n^k.  The word "cycle" denotes different objects (a cyclic vertex
      sequence inside G vs. the base graph cycle_graph n underlying a power),
      and an edge-length / peripheral-cycle assignment yields no bound on a
      cover by equivalence subgraphs (nor vice versa).  No direction holds —
      refuted-direction, not stated.

    • No pair is CONTRADICTORY, so there is no refutation edge
      ([A_statement -> ~ B_statement]) either: all five Props are simultaneously
      satisfiable (they speak about unrelated objects over independent
      carriers), so none refutes another.

    • There is no literature-MOTIVATED candidate direction among the five, so no
      candidate annotation is recorded.

    The file is self-contained: it [Require Import]s the node definitions from
    [Extremal.conjectures.D2str] so the edge endpoints are in scope, re-checks
    that all five are well-typed [Prop]s, and is axiom-free — no
    Conjecture/Axiom/Parameter/Admitted, and no [Theorem … Qed] asserting an
    unproven (or vacuously-forced) edge. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra.
From Extremal.conjectures Require Import D2str.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoints in scope (sanity): the five D2str nodes are well-typed Props. *)
Check linear_hypergraphs_with_dimension_3_statement : Prop.
Check geodesic_cycles_and_tuttes_theorem_statement : Prop.
Check nearly_spanning_regular_subgraphs_statement : Prop.
Check simultaneous_partition_of_hypergraphs_statement : Prop.
Check covering_powers_of_cycles_with_equivalence_subgraphs_statement : Prop.

(** ** Edges.

    No verified-literature edge exists among the five D2str nodes, so no
    [Theorem … Qed] is asserted here, and there is no literature-motivated
    candidate direction to record.  The machine-readable annotations below
    document the two structurally-closest pairs and WHY each is a non-edge, so
    the federated edge extractor records them as refuted-direction (not to be
    stated) rather than leaving a silent gap. *)

(*@EDGE from=linear_hypergraphs_with_dimension_3_statement to=simultaneous_partition_of_hypergraphs_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; these two problems are independent OPG hypergraph entries" note="Non-edge. The only two D2str nodes sharing a hypergraph carrier (T:finType, {set {set T}}), but independent: Row 1 assumes a LINEAR dim-3 hypergraph and concludes a plane triangle/segment representation; Row 4 assumes two r-UNIFORM families and concludes a single rainbow-dense r-partition. Neither hypothesis class contains the other and neither conclusion transports. No reduction/specialisation in either direction. Not stated." *)

(*@EDGE from=geodesic_cycles_and_tuttes_theorem_statement to=covering_powers_of_cycles_with_equivalence_subgraphs_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; independent OPG entries (Tutte geodesic cycles vs equivalence covering number of C_n^k)" note="Non-edge. Both mention 'cycles' but denote different objects: Row 2 is a metric/peripheral-cycle existence statement over arbitrary 3-connected G; Row 5 is an Omega(k) lower bound on the equivalence covering number of the specific family C_n^k. An edge-length/peripheral assignment yields no bound on a cover by equivalence subgraphs (nor vice versa). No direction holds. Not stated." *)
