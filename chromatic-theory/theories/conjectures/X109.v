(** * Chromatic.conjectures.X109 -- v2 Cereceda recolouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X109 vocabulary ***********************************************)

Definition x109_proper_colouring
    (G : sgraph) (q : nat) (col : {ffun G -> 'I_q}) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==> (col x != col y)]].

Definition x109_recolour_step
    (G : sgraph) (q : nat) (c d : {ffun G -> 'I_q}) : bool :=
  [exists v : G,
     (c v != d v) &&
     [forall u : G, (u == v) || (c u == d u)]].

Definition x109_recolour_walk
    (G : sgraph) (q : nat)
    (c d : {ffun G -> 'I_q}) (w : seq {ffun G -> 'I_q}) : Prop :=
  path (x109_recolour_step (G := G) (q := q)) c w /\
  last c w = d /\
  all (x109_proper_colouring (G := G) (q := q)) (c :: w).

Definition x109_recolour_diameter_at_most
    (G : sgraph) (q bound : nat) : Prop :=
  forall c d : {ffun G -> 'I_q},
    x109_proper_colouring c ->
    x109_proper_colouring d ->
    exists w : seq {ffun G -> 'I_q},
      size w <= bound /\ x109_recolour_walk c d w.

(** ** X109 statements *****************************************************)

(** Studies slice: Cereceda's conjecture: the recolouring graph R_{k+2}(G) of
    a k-degenerate n-vertex graph has diameter O(n^2). *)
Definition cereceda_degenerate_recolouring_quadratic_diameter_statement : Prop :=
  exists C : nat,
    forall (k n : nat) (G : sgraph),
      #|G| = n ->
      k_degenerate G k ->
      x109_recolour_diameter_at_most G (k + 2) (C * n ^ 2).
