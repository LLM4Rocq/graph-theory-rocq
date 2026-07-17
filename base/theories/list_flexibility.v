(** * GTBase.list_flexibility -- weighted list-flexibility predicates *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Weight of all requests induced by a list assignment [L].  A weighted
    request is represented directly by [w v c], the weight assigned to the
    request "vertex [v] receives colour [c]". *)
Definition weighted_request_total
    (G : sgraph) (C : finType) (L : G -> {set C}) (w : G -> C -> nat) : nat :=
  \sum_(v : G) \sum_(c in L v) w v c.

Definition weighted_request_satisfied
    (G : sgraph) (C : finType) (w : G -> C -> nat) (f : G -> C) : nat :=
  \sum_(v : G) w v (f v).

Definition proper_list_colouring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [weighted_epsilon_flexible G k p q] says every list assignment with lists
    of size at least [k] and every weighted request admits a proper list
    colouring satisfying at least a [p/q] fraction of the total request weight.
    The rational inequality is cross-multiplied over [nat]. *)
Definition weighted_epsilon_flexible (G : sgraph) (k p q : nat) : Prop :=
  0 < p /\ p <= q /\
  forall (C : finType) (L : G -> {set C}) (w : G -> C -> nat),
    (forall v : G, k <= #|L v|) ->
    exists f : G -> C,
      proper_list_colouring L f /\
      p * weighted_request_total L w <= q * weighted_request_satisfied w f.

(** The unweighted request form: each vertex requests one listed colour. *)
Definition request_satisfied
    (G : sgraph) (C : finType) (r f : G -> C) (v : G) : nat :=
  if f v == r v then 1 else 0.

Definition epsilon_flexible (G : sgraph) (k p q : nat) : Prop :=
  0 < p /\ p <= q /\
  forall (C : finType) (L : G -> {set C}) (r : G -> C),
    (forall v : G, k <= #|L v|) ->
    (forall v : G, r v \in L v) ->
    exists f : G -> C,
      proper_list_colouring L f /\
      p * #|G| <= q * \sum_(v : G) request_satisfied r f v.

(** Basic sanity: the rational parameters are part of the predicate, not an
    external convention. *)
Lemma weighted_epsilon_flexible_params (G : sgraph) (k p q : nat) :
  weighted_epsilon_flexible G k p q -> 0 < p /\ p <= q.
Proof. by move=> [p0 [pq _]]. Qed.

Lemma epsilon_flexible_params (G : sgraph) (k p q : nat) :
  epsilon_flexible G k p q -> 0 < p /\ p <= q.
Proof. by move=> [p0 [pq _]]. Qed.
