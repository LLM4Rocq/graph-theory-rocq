(** * Minor.conjectures.X200 -- v2 Erdos-Posa planar model bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X200 vocabulary ***********************************************)

Definition x200_minor_model (G H : sgraph) (branch : H -> {set G}) : Prop :=
  (forall h : H, branch h != set0) /\
  (forall h : H, connected (branch h)) /\
  (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
  (forall h1 h2 : H, h1 -- h2 ->
    exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x200_model_vertices (G H : sgraph) (branch : H -> {set G}) : {set G} :=
  \bigcup_(h : H) branch h.

Definition x200_k_disjoint_H_models (G H : sgraph) (k : nat) : Prop :=
  exists branch : 'I_k -> H -> {set G},
    (forall i : 'I_k, @x200_minor_model G H (branch i)) /\
    forall i j : 'I_k, i != j ->
      @x200_model_vertices G H (branch i) :&:
      @x200_model_vertices G H (branch j) = set0.

Definition x200_H_model_hitting_set (G H : sgraph) (X : {set G}) : Prop :=
  forall branch : H -> {set G},
    @x200_minor_model G H branch -> @x200_model_vertices G H branch :&: X != set0.

Definition x200_H_model_erdos_posa_oklogk (H : sgraph) : Prop :=
  exists C : nat,
    forall (G : sgraph) (k : nat),
      1 <= k ->
      x200_k_disjoint_H_models G H k \/
      exists X : {set G},
        #|X| <= C * k * (trunc_log 2 k.+1).+1 /\ @x200_H_model_hitting_set G H X.

(** ** X200 statements *****************************************************)

(** Conjecture 1.2 from the wheel-minor paper: for every planar [H], [H]-models
    have the Erdos-Posa property with [O(k log k)] bounding function. *)
Definition planar_H_model_erdos_posa_oklogk_statement : Prop :=
  forall H : sgraph,
    wagner_planar H ->
    x200_H_model_erdos_posa_oklogk H.
