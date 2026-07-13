(** * GTMisc.conjectures.X91 -- v2 avoidable path row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X91 vocabulary ************************************************)

Definition x91_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x91_induced_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x91_consecutive_in_path p u v
  end.

Definition x91_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  (u, v) \in zip c (rot 1 c) \/ (v, u) \in zip c (rot 1 c).

Definition x91_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  3 <= size c /\
  forall u v : G,
    u \in c -> v \in c -> u -- v -> u != v ->
    x91_consecutive_in_cycle c u v.

Definition x91_sequence_contained (G : sgraph) (p c : seq G) : Prop :=
  forall v : G, v \in p -> v \in c.

Definition x91_avoidable_path (G : sgraph) (p : seq G) : Prop :=
  x91_induced_path p /\
  forall u v : G,
    x91_induced_path (u :: rcons p v) ->
    exists c : seq G,
      x91_induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition x91_Pk_free (G : sgraph) (k : nat) : Prop :=
  forall p : seq G, size p = k -> ~ x91_induced_path p.

(** ** X91 statements ******************************************************)

(** Studies slice: Beisegel-Chudnovsky-Gurvich-Milanic-Servatius conjecture:
    every graph either has no induced copy of [P_k] or contains an avoidable
    induced copy of [P_k].  Avoidability is spelled as the standard extension
    property: every induced two-sided extension lies in an induced cycle. *)
Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      x91_Pk_free G k \/
      exists p : seq G, size p = k /\ x91_avoidable_path p.
