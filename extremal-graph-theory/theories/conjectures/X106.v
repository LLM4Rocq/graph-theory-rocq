(** * Extremal.conjectures.X106 -- v2 universal tree-limit row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X105.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X106 vocabulary ***********************************************)

Definition x106_density_close_to
    (H G : sgraph) (C : {set {set G}}) (num den q : nat) : Prop :=
  let total := 'C(#|G|, #|H|) in
  (q * den * #|C| <= (q * num + den) * total) /\
  ((q * num - den) * total <= q * den * #|C|).

Definition x106_density_converges_to
    (H : sgraph) (Tseq : nat -> sgraph) (num den : nat) : Prop :=
  0 < den /\
  forall q : nat,
    0 < q ->
    exists N : nat,
      forall (n : nat) (C : {set {set Tseq n}}),
        N <= n ->
        @x105_induced_copy_family H (Tseq n) C ->
        @x106_density_close_to H (Tseq n) C num den q.

(** ** X106 statements *****************************************************)

(** Studies slice: Bubeck-Linial problem asking for a convergent sequence of
    trees in which every fixed tree has positive limiting induced density. *)
Definition universal_convergent_tree_sequence_positive_density_statement : Prop :=
  exists Tseq : nat -> sgraph,
    (forall n : nat, is_tree [set: Tseq n]) /\
    forall S : sgraph,
      is_tree [set: S] ->
      exists num den : nat,
        0 < num /\ x106_density_converges_to S Tseq num den.
