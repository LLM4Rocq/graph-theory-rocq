(** * Topological.conjectures.grounding_U13 — grounding lemmas for milestone U13.

    SIMPLE, Qed-closed sanity results validating the NEW primitives introduced
    in [U13.v].  For each new definition we record a SATISFIABLE witness and at
    least one textbook identity.  These are statement-validation lemmas, NOT the
    (planarity-gated, open) conjectures themselves — none of them instantiate the
    real planarity oracle, so they are entirely G2-independent.

    New primitives covered:
      - [union_of_two_planar] (row 2, AREA-SPECIFIC): satisfiable for the
        always-true oracle (every graph is its own edge-union, thickness 1);
        monotone in the planarity oracle.  Plus the row-2 non-vacuity guard
        [exists G0, union_of_two_planar … G0] is itself satisfiable.
      - [k_degenerate_on] (row 4, [@MOVE-to-base]): satisfiable — every graph is
        [#|G|]-degenerate on any [W] (the within-[S] degree never exceeds [#|G|]);
        monotone in [k]; hereditary in the host set [W].
      - [k_degenerate] (row 4, [@MOVE-to-base]): the whole-graph specialisation —
        definitional unfolding identity, [#|G|]-degeneracy witness, monotone in k.

    Reused primitives ([Delta], [graph_power], [is_forest], [χ], [N]) are NOT
    re-grounded here: they come verbatim from base / coq-graph-theory. *)

From GTBase Require Import base.
From Topological.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    [union_of_two_planar] — edge-union of two oracle-planar layers.
    ========================================================================== *)

(** ** witness: for the always-true oracle, EVERY graph is the edge-union of two
    "planar" layers — take its own edge relation as the first layer and the empty
    relation as the second (thickness 1 ≤ 2).  So the primitive is satisfiable. *)
Lemma union_of_two_planar_witness (G : sgraph) :
  union_of_two_planar (fun _ : sgraph => True) G.
Proof.
exists (@edge_rel G), (fun _ _ => false), (@sg_sym G), (@sg_irrefl G).
have s2 : symmetric (fun _ _ : G => false) by [].
have i2 : irreflexive (fun _ _ : G => false) by [].
by exists s2, i2; split=> // x y; rewrite orbF.
Qed.

(** ** non-vacuity of the row-2 guard: the existence premise of
    [earth_moon_statement] is satisfiable (for the always-true oracle). *)
Lemma earth_moon_guard_sat :
  exists G0 : sgraph, union_of_two_planar (fun _ : sgraph => True) G0.
Proof. by exists 'K_1; exact: union_of_two_planar_witness. Qed.

(** ** textbook identity: [union_of_two_planar] is monotone in the planarity
    oracle — a weaker oracle accepts at least as many edge-unions. *)
Lemma union_of_two_planar_mono (P Q : sgraph -> Prop) (G : sgraph) :
  (forall H : sgraph, P H -> Q H) ->
  union_of_two_planar P G -> union_of_two_planar Q G.
Proof.
move=> PQ [e1 [e2 [s1 [i1 [s2 [i2 [H1 H2 H3]]]]]]].
exists e1, e2, s1, i1, s2, i2.
by split=> //; [exact: PQ H1 | exact: PQ H2].
Qed.

(** ============================================================================
    [k_degenerate_on] — within-set (induced) degeneracy on a host set [W].
    ========================================================================== *)

(** ** witness: every graph is [#|G|]-degenerate on any host set [W] — within any
    nonempty [S], the chosen vertex's within-[S] degree is at most [#|G|].  So the
    primitive is satisfiable (and the proof genuinely exercises a nonempty [S],
    hence is not vacuous). *)
Lemma k_degenerate_on_max (G : sgraph) (W : {set G}) :
  k_degenerate_on W #|G|.
Proof. by move=> S _ /set0Pn[x xS]; exists x; split=> //; apply: max_card. Qed.

(** ** textbook identity: degeneracy is monotone in the degree bound [k]. *)
Lemma k_degenerate_on_mono (G : sgraph) (W : {set G}) (k k' : nat) :
  (k <= k')%N -> k_degenerate_on W k -> k_degenerate_on W k'.
Proof.
move=> le H S subW Sne; case: (H S subW Sne) => x [xS Hx].
by exists x; split=> //; apply: leq_trans Hx le.
Qed.

(** ** textbook identity: degeneracy is hereditary in the host set — restricting
    [W] to a smaller [W'] preserves [k]-degeneracy (any [S ⊆ W'] is [⊆ W]). *)
Lemma k_degenerate_on_subset (G : sgraph) (W W' : {set G}) (k : nat) :
  W' \subset W -> k_degenerate_on W k -> k_degenerate_on W' k.
Proof.
move=> sub H S subW' Sne; apply: H => //.
exact: subset_trans subW' sub.
Qed.

(** ============================================================================
    [k_degenerate] — whole-graph degeneracy ([k_degenerate_on [set:G]]).
    ========================================================================== *)

(** ** definitional identity: whole-graph degeneracy is host-set degeneracy on
    the full vertex set. *)
Lemma k_degenerateE (G : sgraph) (k : nat) :
  k_degenerate G k = k_degenerate_on [set: G] k.
Proof. by []. Qed.

(** ** witness: every graph is [#|G|]-degenerate. *)
Lemma k_degenerate_max (G : sgraph) : k_degenerate G #|G|.
Proof. exact: k_degenerate_on_max. Qed.

(** ** textbook identity: whole-graph degeneracy is monotone in [k]. *)
Lemma k_degenerate_mono (G : sgraph) (k k' : nat) :
  (k <= k')%N -> k_degenerate G k -> k_degenerate G k'.
Proof. exact: k_degenerate_on_mono. Qed.

(** ============================================================================
    Axiom-freeness audit: the four milestone-U13 statements and the grounding
    lemmas are all closed under the global context (no Parameter/Axiom).
    ========================================================================== *)

Print Assumptions large_induced_forest_in_a_planar_graph_statement.
Print Assumptions earth_moon_statement.
Print Assumptions colouring_the_square_of_a_planar_graph_statement.
Print Assumptions degenerate_colorings_of_planar_graphs_statement.

Print Assumptions union_of_two_planar_witness.
Print Assumptions union_of_two_planar_mono.
Print Assumptions k_degenerate_on_max.
Print Assumptions k_degenerate_on_mono.
Print Assumptions k_degenerate_on_subset.
Print Assumptions k_degenerate_max.

(** ============================================================================
    [is_forest] (coq-graph-theory, reused by row 1) — inhabitation witness.
    ========================================================================== *)

(** ** witness: the empty vertex set is a forest.  This grounds the [is_forest S]
    conclusion of the row-1 existential ([exists S, is_forest S /\ …]) with a
    concrete satisfying [S = set0]: any irredundant path contained in [set0] would
    have its start vertex in [set0] (impossible), so the uniqueness clause of
    [is_forest] holds vacuously. *)
Lemma is_forest0 (G : sgraph) : is_forest (set0 : {set G}).
Proof.
move=> x y p q [_ pS] _.
have xS : x \in (set0 : {set G}) by apply: (subsetP pS); exact: path_begin.
by rewrite in_set0 in xS.
Qed.

Print Assumptions is_forest0.
