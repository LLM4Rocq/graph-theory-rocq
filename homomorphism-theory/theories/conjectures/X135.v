(** * Hom.conjectures.X135 -- v2 Engbers homomorphism-count row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X135 vocabulary ***********************************************)

(** Graph homomorphism count, matching the D2tur local idiom: functions
    [G -> H] preserving adjacency, counted over the finite-function space. *)
Definition x135_hom_count (G H : sgraph) : nat :=
  #|[set f : {ffun G -> H} |
      [forall x : G, [forall y : G, (x -- y) ==> (f x -- f y)]]]|.

Definition x135_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

Definition x135_power_denominator (delta : nat) : nat :=
  2 * delta * delta.+1.

Definition x135_engbers_bound (delta n : nat) (H : sgraph) : nat :=
  maxn
    ((x135_hom_count 'K_(delta.+1) H) ^ (n * (2 * delta)))
    (maxn
       ((x135_hom_count (KB delta delta) H) ^ (n * delta.+1))
       ((x135_hom_count (KB delta (n - delta)) H) ^
          x135_power_denominator delta)).

(** ** X135 statements *****************************************************)

(** Engbers: for fixed delta>=1 and H, sufficiently large n-vertex graphs G of
    minimum degree at least delta maximize hom(G,H) among one of three model
    graphs.  Fractional exponents are cleared by raising the source inequality
    to D = 2*delta*(delta+1); the three right-hand terms then have integral
    exponents n*2delta, n*(delta+1), and D. *)
Definition engbers_homomorphism_count_maximisation_statement : Prop :=
  forall (delta : nat) (H : sgraph),
    1 <= delta ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        x135_min_degree_at_least G delta ->
        (x135_hom_count G H) ^ x135_power_denominator delta
          <= x135_engbers_bound delta n H.

