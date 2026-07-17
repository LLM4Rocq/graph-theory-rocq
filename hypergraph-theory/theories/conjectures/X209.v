(** * Hypergraph.conjectures.X209 -- v2 hypergraph cut excess row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X209 vocabulary ***********************************************)

Definition x209_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

Definition x209_cut_edge
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [exists x in e, [exists y in e, col x != col y]].

Definition x209_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | x209_cut_edge col e]|.

Definition x209_is_max_r_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    x209_cut_size E col = c /\
    forall col' : T -> 'I_r, x209_cut_size E col' <= c.

(** Scale the excess by [r^(k-1)] to avoid rationals:
    [den * maxcut - (den - 1) * m], where [den = r^(k-1)]. *)
Definition x209_expected_den (r k : nat) : nat := r ^ k.-1.

Definition x209_scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    x209_is_max_r_cut E r c /\
    x = x209_expected_den r k * c - (x209_expected_den r k).-1 * #|E|.

Definition x209_is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, x209_scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          x209_scaled_excess E' r k y ->
          x <= y].

(** ** X209 statements *****************************************************)

(** Conlon-Fox-Kwan-Sudakov plausible conjecture, later disproved: for fixed
    [2 <= r <= k], the smallest maximum [r]-cut over [m]-edge [k]-graphs has
    excess [Theta(sqrt m)].  The excess is scaled by the fixed denominator
    [r^(k-1)], which does not change the [Theta(sqrt m)] order for fixed
    [r,k]; the square-root envelope is expressed as [excess(m)^2 = Theta(m)]. *)
Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, x209_is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).
