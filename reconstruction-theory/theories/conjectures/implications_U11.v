(** * Reconstruction.conjectures.implications_U11 — milestone U11 edge spine.

    Implication / refutation EDGES among the four U11 terminal statements of
    [conjectures.U11]:

      (R1) switching_reconstruction_statement                       (Stanley)
      (R2) edge_reconstruction_statement                            (Harary)
      (R3) grahams_conjecture_on_tree_reconstruction_statement      (Graham)
      (R4) reconstruction_statement                                 (Kelly–Ulam)

    Each edge is a RELATIVE theorem [Theorem <A>_implies_<B> : A -> B] meant to
    be [Qed]-closed WITHOUT resolving either endpoint conjecture.  Per the edge
    policy (OPG_FULL_FORMALIZATION_PLAN.md §6) only 'verified-literature' edges
    that carry exact endpoint formulations + citation are scheduled as real
    theorems; 'candidate' edges are recorded as annotation-only until they have
    been re-derived through the [Qed] gate.

    FINDINGS for U11 (see the per-edge analysis below):

    * The ONLY genuine inter-conjecture implication in the reconstruction
      literature among these four nodes is

          reconstruction_statement  ==>  edge_reconstruction_statement

      (Greenwell 1971: the Vertex Reconstruction Conjecture implies the Edge
      Reconstruction Conjecture).  Mathematically this is verified-literature,
      but it is NOT one of the textbook edges enumerated in §6's verified table,
      and its proof is a real combinatorial argument (Kelly-type counting of the
      edge-deck from the vertex-deck, via Nash-Williams' lemma).  It is NOT a
      free relative theorem and cannot be [Qed]-closed without importing that
      counting machinery — i.e. not provable "without resolving" at the level of
      a thin logical implication between the two [Prop]s as formalized here.
      Hence it is recorded as a CANDIDATE edge (proved=false), annotation-only;
      it must be re-derived (Kelly's Lemma over the [vdel_card] / [sdel_edge]
      decks) before it can graduate to a verified [Theorem].

    * The other pairs carry NO known literature implication and therefore NO
      edge is asserted:
        - switching reconstruction (R1, a Seidel-switching-class problem) is
          independent of vertex/edge reconstruction — no implication is known in
          either direction; asserting one would be unfounded.
        - Graham's tree problem (R3) is an independent open problem about the
          iterated-line-graph order sequence of trees; it has no known
          implication to or from R1/R2/R4.

    * NO refuted-direction edge applies here: none of the FALSE/withdrawn edges
      listed in the policy (Reed=>Borodin–Kostochka, list-total=>Behzad,
      list-Hadwiger=>Hadwiger, Caccetta–Häggkvist=>Seymour) involves a U11 node.

    Consequently this file schedules ZERO verified theorems and ONE candidate
    annotation.  It compiles green and is axiom-free (it only [Require]s the U11
    statement module so the endpoint names resolve). *)

From Reconstruction Require Export conjectures.U11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ----------------------------------------------------------------------------
    EDGE 1 (CANDIDATE).  Vertex reconstruction ==> edge reconstruction.

    Exact endpoints (as formalized in [conjectures.U11]):
      from : reconstruction_statement
             [forall G H, 3 <= #|G| -> 3 <= #|H| -> same_deck G H ->
              inhabited (G ≃ H)]
      to   : edge_reconstruction_statement
             [forall G, 4 <= #|E(G)| -> edge_reconstructible G]

    Citation: D. L. Greenwell, "Reconstruction of graphs", Proc. Amer. Math.
    Soc. 30 (1971) 431–433; see also Bondy, "A graph reconstructor's manual"
    (1991), and Lauri–Scapellato, "Topics in Graph Automorphisms and
    Reconstruction".  The implication holds, but its proof needs Kelly's Lemma
    (deriving counts of edge-deleted subgraphs from the vertex-deck) — it is NOT
    a thin logical entailment between the two [Prop]s as stated, so it is left
    as a candidate (proved=false) rather than forced as a verified [Theorem].

    (*@EDGE from=reconstruction_statement to=edge_reconstruction_statement kind=implies status=candidate proved=false cite="Greenwell, Proc. AMS 30 (1971) 431-433; Bondy, A graph reconstructor's manual (1991)" note="Vertex Reconstruction Conjecture implies Edge Reconstruction Conjecture; proof needs Kelly's Lemma counting (not a free relative theorem on these Props), must be re-derived before it can graduate to a verified Qed theorem" *)
    -------------------------------------------------------------------------- *)
