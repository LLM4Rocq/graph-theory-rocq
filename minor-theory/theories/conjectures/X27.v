(** * Minor.conjectures.X27 -- v2 bounded treewidth row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X27 vocabulary ************************************************)

Definition x27_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, [exists t : T, v \in bag t]) /\
  (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\
  forall v : G, connected [set t : T | v \in bag t].

Definition x27_treewidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition x27_consecutive_in_cycle (G : sgraph) (c : seq G) (x y : G) : bool :=
  ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

Definition x27_hole (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 3 < size c /\
  forall x y : G,
    x \in c -> y \in c -> x -- y -> x != y ->
    x27_consecutive_in_cycle c x y.

Definition x27_even_hole_free (G : sgraph) : Prop :=
  forall c : seq G,
    x27_hole c ->
    ~~ odd (size c) ->
    False.

(** ** X27 statements ******************************************************)

(** arXiv:2008.05504, bounded-degree even-hole-free treewidth question. *)
Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (d : nat) (G : sgraph),
      Delta G <= d ->
      x27_even_hole_free G ->
      x27_treewidth_at_most G (f d).
