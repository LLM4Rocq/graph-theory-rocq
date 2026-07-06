(** * Minor.conjectures.grounding_U7 — grounding lemmas for milestone U7.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U7.v]: for each new definition we record a SATISFIABLE witness and at
    least one textbook identity.  These are statement-validation lemmas, not the
    (open) conjectures themselves. *)

From GTBase Require Import base.
From GraphTheory Require Import minor connectivity coloring.
From Minor.conjectures Require Import U7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [path_edges] — boundary identity: the empty walk traverses no edges. *)
Lemma path_edges_nil (G : sgraph) : path_edges (G := G) [::] = set0.
Proof. by rewrite /path_edges /=; apply/setP => e; rewrite !inE. Qed.

(** ** [path_edges] — textbook identity: a two-vertex walk [x; y] traverses the
    single edge {x,y}. *)
Lemma path_edges_pair (G : sgraph) (x y : G) :
  path_edges [:: x; y] = [set [set x; y]].
Proof. by rewrite /path_edges /=; apply/setP => e; rewrite !inE. Qed.

(** ** [immersion] — satisfiable witness: every graph immerses the empty graph
    ['K_0] (no vertices to map, no edges to route — all clauses are vacuous). *)
Lemma immersion_K0 (G : sgraph) : immersion G 'K_0.
Proof.
unshelve eexists; first by case.
exists (fun _ _ => [::]); split; [|split]; by case.
Qed.

(** ** [immersion] — textbook identity: every graph immerses ITSELF (reflexivity)
    via the identity branch map and the one-step walks [u :: [:: v]] along each
    edge; distinct edges give distinct singleton edge-sets, hence edge-disjoint
    walks. *)
Lemma immersion_refl (G : sgraph) : immersion G G.
Proof.
exists id, (fun _ v => [:: v]); split; [|split].
- exact: inj_id.
- by move=> u v uv; split; first by rewrite /= uv.
- move=> u1 v1 u2 v2 _ _ ne.
  by rewrite !path_edges_pair disjoints1 inE.
Qed.

(** ** [average_degree_geq] — satisfiable witness: the [0/b] bound holds for any
    graph (the average degree is always [>= 0]). *)
Lemma average_degree_geq_0 (G : sgraph) (b : nat) : average_degree_geq G 0 b.
Proof. by rewrite /average_degree_geq mul0n. Qed.

(** ** [average_degree_geq] — textbook identity: the numerator bound is
    downward-closed, i.e. a smaller required average is still met. *)
Lemma average_degree_geq_monoL (G : sgraph) (a a' b : nat) :
  a <= a' -> average_degree_geq G a' b -> average_degree_geq G a b.
Proof.
rewrite /average_degree_geq => le H; apply: leq_trans H; exact: leq_mul.
Qed.

(** ** [planar_after_deleting] — satisfiable witness: deleting [0] vertices
    (the empty set) trivially satisfies the [True] planarity predicate. *)
Lemma planar_after_deleting_0 (G : sgraph) :
  planar_after_deleting (fun _ => True) G 0.
Proof. by exists set0; split; first exact: cards0. Qed.

(** ** [apex] — satisfiable witness: the one-vertex graph is apex w.r.t. the
    trivial [True] planarity predicate. *)
Lemma apex_K1 : apex (fun _ => True) 'K_1.
Proof. by exists ord0. Qed.

(** ** [apex] / [planar_after_deleting] — textbook identity linking the two
    primitives: an apex graph becomes planar after deleting (exactly) one
    vertex. *)
Lemma apex_planar_after_deleting
    (is_planar : sgraph -> Prop) (G : sgraph) :
  apex is_planar G -> planar_after_deleting is_planar G 1.
Proof.
by move=> [v Hv]; exists [set v]; split; first exact: cards1.
Qed.

(** ** [wagner_planar] — inhabitation: ['K_4] is Wagner-planar.  Neither ['K_5]
    (a 4-vertex graph cannot have a 5-vertex minor, [small_K_free]) nor [K3,3]
    (6 vertices > 4, [minor_card]) is a minor of ['K_4].  Grounds the planarity
    predicate of Rows 4/5 with a canonical positive witness. *)
Lemma K4_wagner_planar : wagner_planar 'K_4.
Proof.
split.
- apply: (@small_K_free 4 'K_4); by rewrite card_ord.
- move=> H0; move: (minor_card H0); rewrite card_sum !card_ord => Hle.
  by move: Hle.
Qed.

(** ** [wagner_planar] — guard has teeth: ['K_5] is NOT Wagner-planar, since it
    contains itself as a minor ([sub_minor] on [sub_Kn]), i.e. [minor 'K_5 'K_5]
    holds, refuting the first conjunct.  Rules out an accidentally-always-true
    [wagner_planar] that would make Rows 4/5 vacuous. *)
Lemma K5_not_wagner_planar : ~ wagner_planar 'K_5.
Proof.
move=> [Hno5 _]; apply: Hno5; apply: sub_minor.
apply: (@sub_Kn 5 'K_5); by rewrite card_ord.
Qed.

(** ** [minor _ 'K_6] — guard has teeth: ['K_5] has NO K6 minor (a 5-vertex
    graph cannot host a 6-vertex minor, [small_K_free]).  Makes the conclusion
    predicate [minor G 'K_6] of Row 1 (forcing a K6 minor) non-vacuous. *)
Lemma K5_no_K6_minor : ~ minor 'K_5 'K_6.
Proof. apply: (@small_K_free 5 'K_5); by rewrite card_ord. Qed.

(** ** [forcing_a_2_regular_minor_statement] — the [0 < #|G|] soundness guard
    has teeth: the empty graph ['K_0] satisfies the average-degree premise
    vacuously ([_ * 0 <= _]) yet has NO nonempty graph [H] ([3 <= t] vertices)
    as a minor ([minor_card] forces [t <= 0]).  This is exactly the unsoundness
    the [0 < #|G|] guard in Row 6 prevents. *)
Lemma forcing_2reg_guard_teeth (t : nat) (H : sgraph) :
  3 <= t -> #|H| = t ->
  average_degree_geq 'K_0 (4 * t - 6) 3 /\ ~ minor 'K_0 H.
Proof.
move=> t3 cardH; split.
- by rewrite /average_degree_geq card_ord muln0.
- move=> /minor_card; rewrite card_ord cardH => cardle.
  by move: (leq_trans t3 cardle).
Qed.
