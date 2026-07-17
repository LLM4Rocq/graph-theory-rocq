(** * Chromatic.conjectures.X159 -- v2 planar DP-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X159 vocabulary ***********************************************)

Definition x159_no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> lo <= size c -> size c <= hi -> False.

Definition x159_correspondence_assignment
    (G : sgraph) (C : G -> G -> 'I_3 -> 'I_3 -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_3, C u v a b = C v u b a) /\
  (forall (u v : G) (a b1 b2 : 'I_3),
    u -- v -> C u v a b1 -> C u v a b2 -> b1 = b2) /\
  (forall (u v : G) (a1 a2 b : 'I_3),
    u -- v -> C u v a1 b -> C u v a2 b -> a1 = a2).

Definition x159_correspondence_colouring
    (G : sgraph) (C : G -> G -> 'I_3 -> 'I_3 -> bool) : Prop :=
  exists col : G -> 'I_3,
    forall u v : G, u -- v -> ~~ C u v (col u) (col v).

Definition x159_correspondence_3_colourable (G : sgraph) : Prop :=
  forall C : G -> G -> 'I_3 -> 'I_3 -> bool,
    x159_correspondence_assignment C ->
    x159_correspondence_colouring C.

(** ** X159 statements *****************************************************)

(** Informal conjecture: every planar graph without cycles of lengths 4..8 has
    correspondence chromatic number at most 3. *)
Definition planar_no_cycles_4_to_8_correspondence_chromatic_three_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    x159_no_cycle_length_between G 4 8 ->
    x159_correspondence_3_colourable G.
