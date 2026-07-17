(** * GTMisc.conjectures.X156 -- v2 random block-tree diameter row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X156 vocabulary ***********************************************)

Definition x156_two_connected_piece (G : sgraph) (B : {set G}) : Prop :=
  2 <= #|B| /\
  connected B /\
  forall v : G, v \in B -> connected (B :\ v).

Definition x156_block_tree_certificate (G : sgraph) (diam : nat) : Prop :=
  exists (T : sgraph) (block : T -> {set G}) (cut : T -> option G),
    [/\ is_tree [set: T],
        (forall v : G, exists t : T, v \in block t),
        (forall t : T, is_forest (block t) \/ x156_two_connected_piece (block t)),
        (forall t u : T, t -- u ->
          exists x : G, cut t = Some x /\ x \in block t /\ x \in block u) &
        forall t u : T, @graph_dist T t u <= diam].

Definition x156_random_block_stable_model
    (R : nat -> finType) (obs : forall n : nat, R n -> sgraph) : Prop :=
  forall (n : nat) (x : R n), #|obs n x| = n.

Definition x156_random_block_tree_diameter_bound
    (R : nat -> finType) (obs : forall n : nat, R n -> sgraph)
    (f : nat -> nat) : Prop :=
  exists good : forall n : nat, pred (R n),
    @fg_whp R (fun _ _ => 1) good /\
    forall (n : nat) (x : R n),
      good n x -> x156_block_tree_certificate (obs n x) (sqrt_ceil n * f n).

(** ** X156 statements *****************************************************)

(** Informal conjecture: the extra sqrt(log n) factor in the random block-tree
    diameter bound can be replaced by any function tending to infinity.  The
    random model is any finite labelled model [R n] with observation map [obs];
    high probability is exact counting over [R n]. *)
Definition block_tree_diameter_bound_improvement_statement : Prop :=
  forall (R : nat -> finType) (obs : forall n : nat, R n -> sgraph) (f : nat -> nat),
    x156_random_block_stable_model obs ->
    (forall N : nat, exists n : nat, N <= n /\ N <= f n) ->
    x156_random_block_tree_diameter_bound obs f.
