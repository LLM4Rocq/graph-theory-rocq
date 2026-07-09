(** * Digraph.conjectures.XE2 -- Erdos solved clean rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_orients_edge (G : sgraph) (r : rel G) : Prop :=
  forall x y : G, x -- y -> (r x y = ~~ r y x).

Definition xe2_uses_only_edges (G : sgraph) (r : rel G) : Prop :=
  forall x y : G, r x y -> x -- y.

Definition xe2_directed_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

Definition xe2_acyclic_rel (V : finType) (r : rel V) : Prop :=
  forall c : seq V, ~ xe2_directed_cycle r c.

Definition xe2_reverse_one_edge (G : sgraph) (r : rel G) (a b : G) : rel G :=
  fun x y =>
    if (x == a) && (y == b) then false
    else if (x == b) && (y == a) then true
    else r x y.

Definition xe2_orientation_stays_acyclic_after_one_reversal
    (G : sgraph) (r : rel G) : Prop :=
  xe2_acyclic_rel r /\
  forall a b : G, r a b ->
    xe2_acyclic_rel (xe2_reverse_one_edge r a b).

Definition xe2_tournament (V : finType) (r : rel V) : Prop :=
  irreflexive r /\
  forall x y : V, x != y -> r x y = ~~ r y x.

Definition xe2_transitive_on (V : finType) (r : rel V) (S : {set V}) : Prop :=
  forall x y z : V,
    x \in S -> y \in S -> z \in S ->
    r x y -> r y z -> r x z.

Definition xe2_transitive_tournament_guarantee (n k : nat) : Prop :=
  (forall r : rel 'I_n,
      xe2_tournament r ->
      exists S : {set 'I_n}, #|S| = k /\ xe2_transitive_on r S) /\
  forall k' : nat,
    (forall r : rel 'I_n,
      xe2_tournament r ->
      exists S : {set 'I_n}, #|S| = k' /\ xe2_transitive_on r S) ->
    k' <= k.

(** Erdos Problems #1006. *)
Definition erdos_1006_statement : Prop :=
  forall G : sgraph,
    girth_geq G 5 ->
    exists r : rel G,
      xe2_uses_only_edges r /\
      xe2_orients_edge r /\
      xe2_orientation_stays_acyclic_after_one_reversal r.

(** Erdos Problems #1216. *)
Definition erdos_1216_statement : Prop :=
  forall n : nat,
    0 < n ->
    xe2_transitive_tournament_guarantee n (trunc_log 2 n).+1.
