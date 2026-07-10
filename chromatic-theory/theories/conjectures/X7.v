(** * Chromatic.conjectures.X7 -- v2 clean chromatic continuation

    A narrow X7 starter batch: five direct chromatic/list-colouring rows whose
    statements reuse the existing finite-graph surface from U4/XE1/XE2. *)

From GraphTheory Require Import minor.
From GTBase Require Export base.
From Chromatic.conjectures Require Import XE1 XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X7 vocabulary *************************************************)

Definition x7_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma x7_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@x7_delete_edges_rel G F).
Proof.
move=> x y; rewrite /x7_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma x7_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@x7_delete_edges_rel G F).
Proof. by move=> x; rewrite /x7_delete_edges_rel sg_irrefl. Qed.

Definition x7_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@x7_delete_edges_sym G F) (@x7_delete_edges_irrefl G F).

Definition x7_no_critical_edge (G : sgraph) (k : nat) : Prop :=
  forall F : {set G},
    F \in @xe1_edge_set G ->
    χ([set: @x7_delete_edges G [set F]]) = k.

Definition x7_edge_deletion_preserves_chromatic
    (G : sgraph) (k r : nat) : Prop :=
  forall R : {set {set G}},
    R \subset @xe1_edge_set G ->
    #|R| <= r ->
    χ([set: @x7_delete_edges G R]) = k.

Definition x7_four_one_graph (G : sgraph) : Prop :=
  χ([set: G]) = 4 /\
  xe1_vertex_critical G 4 /\
  x7_no_critical_edge G 4.

(** ** X7 statements *******************************************************)

(** arXiv:1803.01051, list-chromatic analogue of Reed's conjecture. *)
Definition list_reed_choice_number_statement : Prop :=
  forall (G : sgraph) (ch : nat),
    is_choice_number G ch ->
    ch <= ceil_div (Delta G + 1 + ω([set: G])) 2.

(** arXiv:2110.09403, Problem 1. *)
Definition list_hadwiger_two_t_statement : Prop :=
  forall (t ch : nat) (G : sgraph),
    1 <= t ->
    ~ minor G ('K_t) ->
    is_choice_number G ch ->
    ch <= 2 * t.

(** arXiv:2310.12891, fixed-small-k open case of Erdos's problem. *)
Definition fixed_k_vertex_critical_edge_robust_statement : Prop :=
  forall k r : nat, 4 <= k ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      x7_edge_deletion_preserves_chromatic G k r.

(** arXiv:2408.02400, Problem 1.5. *)
Definition cochromatic_gap_three_statement : Prop :=
  forall k : nat, 5 <= k ->
    exists G : sgraph,
      ω([set: G]) < 5 /\
      xe2_cochromatic_number G k /\
      χ([set: G]) = k + 3.

(** arXiv:2508.08703, Problem 5.2. *)
Definition six_regular_four_one_graph_statement : Prop :=
  exists G : sgraph,
    regular G 6 /\ x7_four_one_graph G.
