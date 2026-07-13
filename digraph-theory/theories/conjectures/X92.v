(** * Digraph.conjectures.X92 -- v2 tournament inversion-number row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X92 vocabulary ************************************************)

Fixpoint x92_after_inversions
    (D : diGraphType) (steps : seq {set D}) : rel D :=
  match steps with
  | [::] => fun u v : D => u --> v
  | A :: rest =>
      fun u v : D =>
        if (u \in A) && (v \in A)
        then x92_after_inversions rest v u
        else x92_after_inversions rest u v
  end.

Definition x92_acyclic_rel (T : finType) (A : rel T) : bool :=
  [forall v : T, [forall w : T, A v w ==> ~~ connect A w v]].

Definition x92_inverts_to_acyclic
    (D : diGraphType) (steps : seq {set D}) : Prop :=
  x92_acyclic_rel (@x92_after_inversions D steps).

Definition x92_tournament_inversion_number_at_most
    (n k : nat) : Prop :=
  forall T : tournament,
    #|T| = n ->
    exists steps : seq {set T},
      size steps <= k /\ @x92_inverts_to_acyclic T steps.

(** ** X92 statements ******************************************************)

(** Studies slice: Belkhechine-Bouaziz-Boudabbous-Pouzet conjecture that the
    maximum number of subset inversions needed to make an n-vertex tournament
    acyclic is at most floor((n-1)/2). *)
Definition tournament_inversion_number_half_bound_statement : Prop :=
  forall n : nat,
    x92_tournament_inversion_number_at_most n (n.-1 %/ 2).
