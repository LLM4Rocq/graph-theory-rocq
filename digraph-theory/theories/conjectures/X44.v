(** * Digraph.conjectures.X44 -- v2 even directed-cycle row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X44 vocabulary ************************************************)

Definition x44_p_strongly_connected (D : diGraphType) (p : nat) : Prop :=
  p < #|D| /\
  forall S : {set D},
    #|S| < p ->
    strongb (induced_digraph ([set: D] :\: S)).

Definition x44_even_dicycle (D : diGraphType) : Prop :=
  exists c : seq D, dicycle c /\ ~~ odd (size c).

(** ** X44 statements ******************************************************)

(** Studies slice: Lovasz even directed cycle conjecture. *)
Definition lovasz_even_directed_cycle_statement : Prop :=
  exists p : nat,
    forall D : diGraphType,
      x44_p_strongly_connected D p ->
      x44_even_dicycle D.
