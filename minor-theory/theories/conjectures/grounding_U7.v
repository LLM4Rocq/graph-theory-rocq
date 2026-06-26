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
