(** * GTMisc.conjectures.XE2 -- Erdős solved clean rows *)

From GTMisc.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe2_triangle_free_rel (V : finType) (r : rel V) : Prop :=
  forall x y z : V, r x y -> r y z -> r z x -> False.

Definition xe2_independent3 (V : finType) (r : rel V) (a b c : V) : Prop :=
  a != b /\ a != c /\ b != c /\ ~~ r a b /\ ~~ r a c /\ ~~ r b c.

(** Erdős Problems #715: "Does every 4-regular graph contain a 3-regular subgraph?
    Is there any r such that every r-regular graph must contain a 3-regular
    subgraph?"  Part (b) requires [3 < r]: at r = 3 the host is itself a
    3-regular subgraph (H := G), so the question is only non-trivial for r > 3
    (part (a) is the first case, r = 4). *)
Definition erdos_715_statement : Prop :=
  (forall G : sgraph, 0 < #|G| -> regular G 4 ->
      exists H : sgraph, 0 < #|H| /\ xe2_subgraph_of H G /\ regular H 3) /\
  (exists r : nat, 3 < r /\
      forall G : sgraph, 0 < #|G| -> regular G r ->
        exists H : sgraph, 0 < #|H| /\ xe2_subgraph_of H G /\ regular H 3).

(** Erdős Problems #895. *)
Definition erdos_895_statement : Prop :=
  exists N : nat,
    forall n : nat, N <= n ->
    forall r : rel 'I_n,
      symmetric r -> irreflexive r -> xe2_triangle_free_rel r ->
      exists a b c : 'I_n,
        (val a).+1 + (val b).+1 = (val c).+1 /\
        xe2_independent3 r a b c.
