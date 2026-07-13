(** * Minor.conjectures.X67 -- v2 theta-triangle bounded-treewidth row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X67 vocabulary ************************************************)

Definition x67_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x67_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set x : G | x \in p].

Definition x67_internal_vertices (G : sgraph) (a b : G) (p : seq G) : {set G} :=
  x67_path_vertices p :\: [set a; b].

Definition x67_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      3 <= size p /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x67_consecutive_in_path p u v
  end.

Definition x67_no_cross_edges
    (G : sgraph) (a b : G) (p q : seq G) : Prop :=
  forall u v : G,
    u \in x67_internal_vertices a b p ->
    v \in x67_internal_vertices a b q ->
    ~~ (u -- v).

Definition x67_theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    x67_induced_path_between a b p1 /\
    x67_induced_path_between a b p2 /\
    x67_induced_path_between a b p3 /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p2] /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p3] /\
    [disjoint x67_internal_vertices a b p2 & x67_internal_vertices a b p3] /\
    x67_no_cross_edges a b p1 p2 /\
    x67_no_cross_edges a b p1 p3 /\
    x67_no_cross_edges a b p2 p3.

(** ** X67 statements ******************************************************)

(** arXiv:2001.01607, theta/triangle-free bounded-degree graphs have bounded
    treewidth. *)
Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ x67_theta G ->
      x27_treewidth_at_most G (f t).
