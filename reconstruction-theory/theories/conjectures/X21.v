(** * Reconstruction.conjectures.X21 -- v2 deck-reconstruction continuation rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X21 vocabulary ************************************************)

Definition x21_l_deck_index (G : sgraph) (ell : nat) : Type :=
  {S : {set G} | #|S| == ell}.

Definition x21_same_l_deck (G H : sgraph) (ell : nat) : Prop :=
  exists f : x21_l_deck_index G ell -> x21_l_deck_index H ell,
    bijective f /\
    forall S : x21_l_deck_index G ell,
      inhabited (induced (val S) ≃ induced (val (f S))).

Definition x21_l_reconstructible (G : sgraph) (ell : nat) : Prop :=
  forall H : sgraph,
    #|H| = #|G| ->
    x21_same_l_deck G H ell ->
    inhabited (G ≃ H).

(** ** X21 statements ******************************************************)

(** Studies slice: Kelly-Manvel reconstruction from the (n-r)-deck. *)
Definition kelly_manvel_n_minus_r_deck_reconstruction_statement : Prop :=
  forall r : nat, exists N : nat,
    r <= N /\
    forall G : sgraph,
      N <= #|G| ->
      x21_l_reconstructible G (#|G| - r).

(** Studies slice: Nydl's tree deck-reconstruction conjecture. *)
Definition nydl_tree_l_deck_reconstruction_statement : Prop :=
  forall (n ell : nat) (T1 T2 : sgraph),
    4 <= n ->
    n./2 + 1 <= ell ->
    #|T1| = n ->
    #|T2| = n ->
    is_tree [set: T1] ->
    is_tree [set: T2] ->
    x21_same_l_deck T1 T2 ell ->
    inhabited (T1 ≃ T2).

(** Studies slice: Spinoza-West connectedness threshold conjecture. *)
Definition spinoza_west_l_deck_connectedness_statement : Prop :=
  forall (n ell : nat) (G H : sgraph),
    6 <= n ->
    n./2 + 1 <= ell ->
    #|G| = n ->
    #|H| = n ->
    x21_same_l_deck G H ell ->
    (connected [set: G] <-> connected [set: H]).
