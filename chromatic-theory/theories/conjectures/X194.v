(** * Chromatic.conjectures.X194 -- v2 clustered colouring minor row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X194 vocabulary ***********************************************)

Definition x194_vertex_ranking (G : sgraph) (k : nat) (rank : G -> 'I_k) : Prop :=
  forall (x y : G) (p : seq G),
    x != y ->
    path (--) x p ->
    last x p = y ->
    rank x = rank y ->
    exists z : G, z \in p /\ rank x < rank z.

Definition x194_treedepth_at_most (G : sgraph) (k : nat) : Prop :=
  exists rank : G -> 'I_k, x194_vertex_ranking rank.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  forall G : sgraph, ~ minor G H -> clustered_chromatic_at_most G k.

(** ** X194 statements *****************************************************)

(** Norin-Scott-Seymour-Wood Conjecture 4: the clustered chromatic number of
    the [H]-minor-free class is at most [2*td(H)-2]. *)
Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      x194_treedepth_at_most H k ->
      x194_clustered_chromatic_minor_class_le H (2 * k - 2).
