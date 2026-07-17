(** * Extremal.conjectures.X125 -- v2 random-lift Hajos number row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X125 vocabulary ***********************************************)

Definition x125_lift (n ell : nat) (G : sgraph) : Prop :=
  exists pi : G -> 'I_n,
    (forall i : 'I_n, #|[set v : G | pi v == i]| = ell) /\
    (forall x y : G, x -- y -> pi x != pi y) /\
    (forall i j : 'I_n, i != j ->
      forall x : G, pi x = i ->
        exists y : G, pi y = j /\ x -- y /\
          forall z : G, pi z = j -> x -- z -> z = y).

Definition x125_topological_minor_K (G : sgraph) (k : nat) : Prop :=
  exists branch : 'K_k -> G,
    injective branch /\
    forall (x y : 'K_k),
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall (u : 'K_k), z != branch u].

Definition x125_hajos_at_least (G : sgraph) (k : nat) : Prop :=
  x125_topological_minor_K G k.

Definition x125_random_lift_space
    (n ell : nat) (L : finType) (obs : L -> sgraph) : Prop :=
  forall x : L, x125_lift n ell (obs x).

Definition x125_almost_all (n ell : nat) (P : sgraph -> Prop) : Prop :=
  forall (L : finType) (obs : L -> sgraph),
    x125_random_lift_space n ell obs ->
    exists good : pred L,
      @fg_event_at_least_ratio L (fun _ => 1) good 9 10 /\
      forall x : L, good x -> P (obs x).

(** ** X125 statements *****************************************************)

(** Studies slice: Drier-Linial conjecture -- for ell >= Omega(n), almost all
    ell-lifts of K_n have Hajos number Theta(n). *)
Definition drier_linial_random_lift_hajos_number_statement : Prop :=
  forall n ell : nat,
    n <= ell ->
    exists a b : nat,
      0 < a /\ 0 < b /\
      x125_almost_all n ell
        (fun G : sgraph =>
           x125_lift n ell G ->
           x125_hajos_at_least G (a * n) /\
           forall k : nat, x125_hajos_at_least G k -> k <= b * n).
