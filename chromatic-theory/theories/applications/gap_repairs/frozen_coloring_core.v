From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FrozenColorings.
Variables (G : sgraph) (C : finType).

Definition fc_coloring := {ffun G -> C}.
Definition fc_closed (x : G) : {set G} := x |: N(x).
Definition fc_proper (f : fc_coloring) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==> (f x != f y)]].
Definition fc_frozen_at (f : fc_coloring) (x : G) : bool :=
  [forall c : C, c \in f @: fc_closed x].
Definition fc_frozen (f : fc_coloring) : bool :=
  [forall x : G, fc_frozen_at f x].
Definition fc_frozen_proper (f : fc_coloring) : bool :=
  fc_proper f && fc_frozen f.
Definition fc_swap (f : fc_coloring) (x y : G) : fc_coloring :=
  [ffun z => if z == x then f y else if z == y then f x else f z].
Definition fc_nontwin (x y : G) : bool :=
  (x -- y) && (fc_closed x != fc_closed y).

End FrozenColorings.
