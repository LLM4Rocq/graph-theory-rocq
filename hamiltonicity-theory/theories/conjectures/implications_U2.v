(** * Hamilton.conjectures.implications_U2 — milestone U2 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the nine committed
    U2 Hamiltonicity statements (see [U2.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer and the chromatic
    [implications_U1.v], every edge here is meant to be a *relative* theorem: a
    [Qed]-closed [Theorem A_statement -> B_statement] provable WITHOUT resolving
    (proving or refuting) either endpoint.  Any bridge fact that would need
    resolving a conjecture or heavy out-of-scope machinery is carried as an
    EXPLICIT hypothesis (never [Admitted], never [Axiom]), keeping the file
    fully [Qed]-closed and axiom-free.

    ────────────────────────────────────────────────────────────────────────
    AUDIT RESULT: no [verified-literature] edge among the nine U2 nodes.
    ────────────────────────────────────────────────────────────────────────

    Cross-check with the plan §6: the verified-literature table carries NO U2
    entry (its rows are CDC / Petersen-colouring / 4-flow, i.e. U6/U10/D1).  The
    only U2-touching catalogued edge is the CANDIDATE
    "prism-hamiltonicity ⟺ hamilton-decomposition-of-prism" — re-derived below
    and REJECTED by the Qed gate as formulated (see Row 5 ↔ Row 7).

    The nine U2 nodes:

      Row 1  hamiltonian_paths_and_cycles_in_vertex_transitive_gr  (VT ⟹ ∃ ham PATH)
      Row 2  hamiltonicity_of_cayley_graphs                        (Cayley ⟹ ham CYCLE)
      Row 3  four_connected_graphs_are_not_uniquely_hamiltonian    (4-conn ⟹ 2nd cycle)
      Row 4  uniquely_hamiltonian_graphs                           (r-reg, r>2 ⟹ ¬unique)
      Row 5  decomposing_the_prism_of_a_3_connected_cubic_planar   (PLANARITY-GATED)
      Row 6  every_4_connected_toroidal_graph_has_a_hamilton_cycl  (TOROIDAL-GATED)
      Row 7  every_prism_over_a_3_connected_planar_graph_is_hamil  (PLANARITY-GATED)
      Row 8  barnettes                                             (PLANARITY-GATED)
      Row 9  hamiltonian_cycles_in_line_graphs                     (4-conn LG ⟹ ham)

    ── Why no pair carries an honest [verified-literature] relative edge ──

    • Row 1 ⇎ Row 2 (Lovász vs the Cayley question).  A [cayley_graph] is
      vertex-transitive and (with generating [S]) connected, so Row 1 applies to
      it — but Row 1 only delivers a Hamiltonian PATH while Row 2 demands a
      Hamiltonian CYCLE (strictly stronger): Row 1 ⇏ Row 2.  Conversely Row 1
      ranges over ALL connected vertex-transitive graphs, a proper superset of
      the Cayley graphs (e.g. the Petersen graph is vertex-transitive, NOT a
      Cayley graph), so the Cayley-only hypothesis of Row 2 cannot reach Row 1:
      Row 2 ⇏ Row 1.  Independent.

    • Row 3 ⇎ Row 4.  Both are flavours of "not uniquely Hamiltonian", but under
      DISJOINT hypothesis classes: Row 3 over 4-connected graphs, Row 4 over
      r-regular (r>2) graphs.  A 4-connected graph need not be regular and an
      r-regular graph need not be 4-connected, so neither hypothesis specializes
      to the other and neither statement transports to the other.  Independent.

    • Rows 5–8 are PLANARITY/GENUS-GATED placeholders (blocked): their geometric
      hypothesis is an ABSTRACT predicate [forall (planar/toroidal : sgraph ->
      Prop), ...].  Being universally quantified, the predicate can be
      instantiated with [fun _ => True], collapsing each blocked row to an
      absurdly strong placeholder-free statement (e.g. Row 6 ⟹ "EVERY
      4-connected graph is Hamiltonian").  Such collapses DO yield compiling
      implications into the real rows (Row 6 ⟹ Row 9 closes with [Qed]) — but
      they are FORMALIZATION ARTIFACTS of the blocked placeholder, NOT literature
      edges (no theorem says "4-connected toroidal Hamiltonicity ⟹ Thomassen's
      4-connected-line-graph conjecture").  Per the edge policy they are NOT
      scheduled; they are recorded as candidate-artifacts in the deliverable's
      edge table, not as Rocq theorems here.

    • Row 5 ↔ Row 7 — the §6 CANDIDATE "prism-hamiltonicity ⟺
      hamilton-decomposition-of-prism" — FAILS the Qed gate as formulated, in
      BOTH directions:
        – Row 5 ⟹ Row 7: a 2-cycle Hamilton decomposition trivially gives a
          Hamilton cycle (lemma [decomp_into_two_is_hamiltonian] below), BUT
          Row 5 only constrains CUBIC graphs while Row 7 quantifies over ALL
          3-connected planar graphs; applying Row 5 inside a proof of Row 7
          leaves the residual goal [regular G 3], which Row 7's hypotheses do
          NOT supply.  Unprovable.
        – Row 7 ⟹ Row 5: Row 7 yields only the EXISTENCE of one Hamilton cycle,
          whereas Row 5 demands a full partition of E(prism) into TWO
          edge-disjoint Hamilton cycles (strictly stronger — even a Hamiltonian
          4-regular graph need not split into two Hamilton cycles).  Unprovable.
      So the candidate stays status=candidate, proved=false.

    Consequently this file commits ZERO conjecture-EDGES: there is no honest
    [verified-literature] node-to-node implication to schedule.  We DO record the
    one robustly-true structural fragment as a LEMMA (not a conjecture-edge, per
    the §6 convention for trivial monotone relations): a 2-cycle Hamilton
    decomposition implies Hamiltonicity.  The file loads axiom-free, so the
    milestone's edge layer is present and green. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup.
From Hamilton.conjectures Require Import U2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Structural fragment (LEMMA, not a conjecture-edge).

    The only robustly-true relation between the U2 primitives that does NOT
    depend on a blocked planarity placeholder: a Hamilton decomposition of [G]
    into two cycles exhibits, in particular, one Hamilton cycle — so [G] is
    Hamiltonian.  This is the honest (and trivial) half of the §6 candidate
    "prism-hamiltonicity ⟺ hamilton-decomposition-of-prism"; the conjectural
    converse (Hamiltonicity ⟹ 2-cycle decomposition) is FALSE and absent.

    It is a relation between PRIMITIVES, not between two node statements, so it
    is recorded as a lemma rather than an [A_implies_B] edge. *)
Lemma decomp_into_two_is_hamiltonian (G : sgraph) :
  hamilton_decomposition_into_two G -> is_hamiltonian G.
Proof. by move=> [c1 [c2 [H1 _ _ _]]]; exists c1. Qed.

(** No conjecture-edge is scheduled: see the AUDIT RESULT above.  Among the nine
    U2 nodes there is no [verified-literature] relative implication; the §6
    candidate (Row 5 ↔ Row 7) is rejected by the Qed gate as formulated, and the
    placeholder-collapse implications out of the blocked Rows 5–8 are
    formalization artifacts, not literature edges, so they are deliberately
    absent here. *)
