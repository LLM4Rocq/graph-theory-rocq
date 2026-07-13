(** * GTMisc.conjectures.X99 -- v2 hat guessing versus Hadwiger row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X99 vocabulary ************************************************)

Definition x99_hat_strategy (G : sgraph) (q : nat) :=
  forall v : G, (G -> 'I_q) -> 'I_q.

Definition x99_local_strategy
    (G : sgraph) (q : nat) (guess : x99_hat_strategy G q) : Prop :=
  forall (v : G) (a b : G -> 'I_q),
    (forall u : G, u -- v -> a u = b u) ->
    guess v a = guess v b.

Definition x99_winning_hat_strategy (G : sgraph) (q : nat) : Prop :=
  exists guess : x99_hat_strategy G q,
    x99_local_strategy guess /\
    forall hats : G -> 'I_q,
      [exists v : G, guess v hats == hats v].

Definition x99_hat_guessing_number_at_most (G : sgraph) (k : nat) : Prop :=
  forall q : nat, k < q -> ~ x99_winning_hat_strategy G q.

Definition x99_hadwiger_number (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\
  forall t : nat, minor G 'K_t -> t <= h.

(** ** X99 statements ******************************************************)

(** Studies slice: Bosek-Dudek-Farnik-Grytczuk-Mazur conjecture that the hat
    guessing number of every graph is at most its Hadwiger number. *)
Definition hat_guessing_number_hadwiger_bound_statement : Prop :=
  forall (G : sgraph) (h : nat),
    x99_hadwiger_number G h ->
    x99_hat_guessing_number_at_most G h.
