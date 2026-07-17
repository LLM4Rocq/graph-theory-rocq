(** * Minor.conjectures.X174 -- v2 clique count without K_t immersion row *)

From GTBase Require Export base.
From Minor.conjectures Require Import U7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X174 vocabulary ***********************************************)

Definition x174_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S]|.

Definition x174_no_Kt_immersion (G : sgraph) (t : nat) : Prop :=
  ~ immersion G 'K_t.

Definition x174_extremal_bound (t n : nat) : nat :=
  (2 ^ (t - 2)) * (n - t + 3).

(** ** X174 statements *****************************************************)

(** Fox-Wei conjecture: the maximum number of cliques in an n-vertex graph with
    no [K_t]-immersion is [2^(t-2)(n-t+3)].  The exact maximum is encoded as
    the universal upper-bound half together with existence of a matching graph. *)
Definition kt_immersion_clique_count_extremal_statement : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        x174_no_Kt_immersion G t ->
        x174_clique_count G <= x174_extremal_bound t n) /\
    (exists G : sgraph,
        #|G| = n /\
        x174_no_Kt_immersion G t /\
        x174_clique_count G = x174_extremal_bound t n).
