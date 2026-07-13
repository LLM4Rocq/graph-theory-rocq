(** * Digraph.conjectures.X79 -- v2 tournament Erdos-Hajnal row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X79 vocabulary ************************************************)

Definition x79_transitive_subtournament_at_least
    (T : tournament) (a : nat) : Prop :=
  exists S : {set T}, a <= #|S| /\ transb (sub_tournament S).

Definition x79_polynomial_transitive_bound
    (eps_num eps_den n a : nat) : Prop :=
  n ^ eps_num <= a ^ eps_den.

(** ** X79 statements ******************************************************)

(** Studies slice: Alon-Pach-Solymosi tournament Erdos-Hajnal conjecture. *)
Definition alon_pach_solymosi_tournament_erdos_hajnal_statement : Prop :=
  forall H : tournament,
    exists eps_num eps_den : nat,
      [/\ 0 < eps_num, 0 < eps_den
        & forall T : tournament,
            ind_free H T ->
            exists a : nat,
              x79_transitive_subtournament_at_least T a /\
              x79_polynomial_transitive_bound eps_num eps_den #|T| a].
