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
(* [minor] is [Require Import]-ed (not Export-ed) by base; row-1 fragments below
   use [small_K_free] / [non_forerst_K3] from it, so re-import here. *)
From GraphTheory Require Import minor.

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

(** ============================================================================
    Row 1 — [large_induced_forest_in_a_planar_graph_statement] right-polarity
    fragments (TECHNIQUE #2).  The FULL n/2 conclusion for an arbitrary
    [wagner_planar] G is the OPEN Albertson–Berman conjecture (and even the best
    settled 2n/5 bound rests on Borodin's acyclic 5-colouring, a major theorem)
    — NOT attempted.  What is grounded here are faithful, Qed-closed fragments
    that pin the statement's truth value where it IS decided and show the
    planarity guard is load-bearing.  All are on the intended object
    ([sgraph] / [wagner_planar] / [is_forest]); none weaken the statement.
    ========================================================================== *)

(** ** always-true direction / forest sub-class: on graphs that ARE forests the
    existential conclusion holds outright by taking [S = set:G] — |S| = n ≥ n/2.
    Pins the conjectured direction TRUE on the whole (planar) forest sub-class. *)
Lemma lif_conclusion_on_forests (G : sgraph) :
  is_forest [set: G] ->
  exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.
Proof.
move=> HF; exists [set: G]; split=> //.
by rewrite cardsT mul2n -addnn leq_addr.
Qed.

(** ** small-instance (n ≤ 2): every graph on at most 2 vertices satisfies the
    full conclusion.  Such a graph has no [K3] minor ([small_K_free]), hence is a
    forest (contrapositive of [non_forerst_K3], decided via [is_forestb] — no
    classical axiom), so [S = set:G] works.  Pins the statement TRUE on the
    decidable n ≤ 2 slice (all of which are planar) and exercises the
    K3-minor-free ⇒ forest link. *)
Lemma lif_small (G : sgraph) :
  (#|G| <= 2)%N ->
  exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.
Proof.
move=> le2.
have nK3 : ~ minor G 'K_3 := small_K_free le2.
have HF : is_forest [set: G].
  case E: (is_forestb [set: G]); first exact/is_forestP.
  exfalso; apply: nK3; apply: non_forerst_K3 => /is_forestP H.
  by rewrite E in H.
exists [set: G]; split=> //.
by rewrite cardsT mul2n -addnn leq_addr.
Qed.

(** ** hypothesis-class richness: EVERY graph on at most 4 vertices is
    [wagner_planar] (a [K5] minor needs 5 vertices, a [K3,3] minor needs 6, by
    [minor_card]).  Shows the planarity guard is far from vacuous — the
    universal [forall G, wagner_planar G -> …] genuinely ranges over the whole
    ≤4-vertex class (paired with [K5_teeth] below this brackets the guard). *)
Lemma wagner_planar_small (G : sgraph) : (#|G| <= 4)%N -> wagner_planar G.
Proof.
move=> le4; split=> Hm; move: (leq_trans (minor_card Hm) le4).
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

(** ** teeth (guard is load-bearing).  In the excluded non-planar [K5] any induced
    forest has at most 2 vertices: an induced forest [S] with [#|S| ≥ 3] yields
    (via [induced_forest] + [forest3]) two distinct non-adjacent vertices, but
    [K5] is complete, contradiction. *)
Lemma K5_forest_le2 (S : {set 'K_5}) : is_forest S -> (#|S| <= 2)%N.
Proof.
move=> HF; rewrite leqNgt; apply/negP => H3.
have HF' := induced_forest HF.
have c3 : (3 <= #|induced S|)%N by rewrite card_sig.
have [x [y [xy nadj]]] := forest3 HF' c3.
move: nadj; rewrite induced_edge /= /edge_rel /= => /negP; apply.
by rewrite /complete_rel /= (inj_eq val_inj).
Qed.

(** Hence the same conclusion is FALSE on [K5]: 5 ≤ 2·#|S| ≤ 2·2 = 4 is
    impossible.  So dropping/weakening the [wagner_planar] guard would REFUTE the
    statement — the planarity hypothesis is genuinely constraining, not
    decorative or vacuizing. *)
Lemma K5_teeth : ~ (exists S : {set 'K_5}, is_forest S /\ (#|'K_5| <= 2 * #|S|)%N).
Proof.
case=> S [/K5_forest_le2 hS]; rewrite card_ord => hb.
by move: (leq_trans hb (leq_mul (leqnn 2) hS)).
Qed.

Print Assumptions lif_conclusion_on_forests.
Print Assumptions lif_small.
Print Assumptions wagner_planar_small.
Print Assumptions K5_forest_le2.
Print Assumptions K5_teeth.

(** ============================================================================
    TECHNIQUE #3 — independent re-encoding of [k_degenerate_on] with a proved
    [<->].

    [k_degenerate_on W k] (base) is the SUBSET-QUANTIFIED characterisation: EVERY
    nonempty [S ⊆ W] contains a vertex of within-[S] degree [≤ k] (a witness per
    subset).  We give the classical ELIMINATION-ORDERING characterisation, encoded
    as a RANK FUNCTION [r : G -> nat] that is injective on [W] (a single linear
    order) such that each [x ∈ W] has [≤ k] neighbours of strictly smaller rank
    ("earlier" in the order).  These are the two textbook definitions of
    degeneracy, structurally opposite: a UNIVERSAL over all [2^{|W|}] subsets vs.
    the EXISTENCE of ONE global order with a LOCAL earlier-neighbour bound.

    The equivalence is genuinely non-trivial (NOT definitional).
    - [rank ⟹ on] (easy half): given the order, the vertex of MAXIMAL rank inside
      any nonempty [S ⊆ W] has all its [S]-neighbours strictly earlier, so its
      within-[S] degree is [≤ k].
    - [on ⟹ rank] (the load-bearing half): strong induction on [#|W|].  Apply the
      degeneracy hypothesis to [S := W] to peel a low-degree vertex [v], recurse on
      [W :\ v] (still degenerate, [k_degenerate_on_subset]) for a rank [r'], and
      extend it by ranking [v] TOP ([r v := #|W|-1]); a bound invariant [r x < #|W|]
      keeps the extended rank injective and the earlier-neighbour count within [k].
    Agreement of the two faithful encodings is the faithfulness evidence for
    [k_degenerate_on].
    ========================================================================== *)

(** Elimination-ordering (rank-function) reading of degeneracy. *)
Definition k_degenerate_rank (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  exists r : G -> nat,
    {in W &, injective r} /\
    (forall x, x \in W -> #|[set y in W | (y \in N(x)) && (r y < r x)]| <= k).

(** Easy half: an elimination order certifies degeneracy (max-rank vertex of any
    nonempty subset has all its neighbours in the subset ranked strictly lower). *)
Lemma kdeg_rank_to_on (G : sgraph) (W : {set G}) (k : nat) :
  k_degenerate_rank W k -> k_degenerate_on W k.
Proof.
move=> [r [rinj rprop]] S subW /set0Pn[x0 x0S].
have [x xS xmax] := arg_maxnP (fun i => r i) x0S.
have xW : x \in W := subsetP subW _ xS.
exists x; split=> //.
apply: leq_trans (rprop x xW).
apply: subset_leq_card; apply/subsetP => y.
rewrite !inE => /andP[yNx yS].
have yW : y \in W := subsetP subW _ yS.
rewrite yW yNx /=.
have yx : y != x by apply/eqP => e; move: yNx; rewrite e sg_irrefl.
rewrite ltn_neqAle; apply/andP; split; last exact: (xmax y yS).
apply/eqP => e; apply/negP: yx; rewrite negbK; apply/eqP; exact: rinj yW xW e.
Qed.

(** Hard half, strengthened for the induction with a rank-bound invariant. *)
Lemma kdeg_on_to_rank_aux (G : sgraph) (k : nat) :
  forall n (W : {set G}), #|W| = n -> k_degenerate_on W k ->
    exists r : G -> nat,
      [/\ {in W &, injective r},
          (forall x, x \in W -> r x < n) &
          (forall x, x \in W -> #|[set y in W | (y \in N(x)) && (r y < r x)]| <= k) ].
Proof.
elim=> [|n IH] W cardW deg.
- move: cardW => /cards0_eq ->.
  exists (fun=> 0); split=> // x; by rewrite inE.
- have Wne : W != set0 by rewrite -card_gt0 cardW.
  have [v [vW Hv]] := deg W (subxx W) Wne.
  have subW' : W :\ v \subset W by exact: subsetDl.
  have cardW' : #|W :\ v| = n by move: cardW; rewrite (cardsD1 v) vW add1n => -[].
  have deg' : k_degenerate_on (W :\ v) k.
    move=> S subS Sne; apply: deg => //; exact: subset_trans subS subW'.
  have [r' [inj' bound' prop']] := IH _ cardW' deg'.
  pose r := fun z => if z == v then n else r' z.
  have rv : r v = n by rewrite /r eqxx.
  have rnv : forall z, z != v -> r z = r' z by move=> z zv; rewrite /r (negbTE zv).
  exists r; split.
  + have inD : forall z, z \in W -> z != v -> z \in W :\ v by
      move=> z zW zv; rewrite in_setD1 zv zW.
    move=> x1 x2 x1W x2W.
    case: (eqVneq x1 v) => [->|x1v]; case: (eqVneq x2 v) => [->|x2v] //.
    * by rewrite rv (rnv _ x2v) => e; move: (bound' x2 (inD _ x2W x2v)); rewrite -e ltnn.
    * by rewrite (rnv _ x1v) rv => e; move: (bound' x1 (inD _ x1W x1v)); rewrite e ltnn.
    * by rewrite (rnv _ x1v) (rnv _ x2v) => e; exact: inj' (inD _ x1W x1v) (inD _ x2W x2v) e.
  + have inD : forall z, z \in W -> z != v -> z \in W :\ v by
      move=> z zW zv; rewrite in_setD1 zv zW.
    move=> x xW; case: (eqVneq x v) => [->|xv].
    * by rewrite rv.
    * by rewrite (rnv _ xv); apply: (leq_trans (bound' x (inD _ xW xv))); exact: leqnSn.
  + have inD : forall z, z \in W -> z != v -> z \in W :\ v by
      move=> z zW zv; rewrite in_setD1 zv zW.
    move=> x xW; case: (eqVneq x v) => [->|xv].
    * rewrite rv; apply: leq_trans Hv; apply: subset_leq_card; apply/subsetP => y.
      by rewrite !inE => /and3P[yW yNv _]; rewrite yNv yW.
    * rewrite (rnv _ xv); apply: leq_trans (prop' x (inD _ xW xv)).
      apply: subset_leq_card; apply/subsetP => y; rewrite !inE => /and3P[yW yNx ryx].
      have yv : y != v.
        apply/eqP => e; move: ryx; rewrite e rv => h.
        by move: (ltn_trans (bound' x (inD _ xW xv)) h); rewrite ltnn.
      by rewrite yv yW yNx -(rnv _ yv).
Qed.

Lemma kdeg_on_to_rank (G : sgraph) (W : {set G}) (k : nat) :
  k_degenerate_on W k -> k_degenerate_rank W k.
Proof.
move=> deg; have [r [ri _ rp]] := kdeg_on_to_rank_aux (erefl #|W|) deg.
by exists r.
Qed.

(** MAIN [<->]: the subset-quantified encoding [k_degenerate_on] agrees with the
    elimination-ordering encoding [k_degenerate_rank].  Axiom-free (below). *)
Lemma k_degenerate_ordP (G : sgraph) (W : {set G}) (k : nat) :
  k_degenerate_on W k <-> k_degenerate_rank W k.
Proof. split; [exact: kdeg_on_to_rank | exact: kdeg_rank_to_on]. Qed.

Print Assumptions k_degenerate_ordP.
