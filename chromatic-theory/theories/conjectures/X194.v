(** * Chromatic.conjectures.X194 -- v2 clustered colouring minor row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X194 vocabulary ***********************************************)

Definition x194_vertex_ranking (G : sgraph) (k : nat) (rank : G -> 'I_k) : Prop :=
  forall (x y : G) (p : seq G),
    x != y ->
    path (--) x p ->
    last x p = y ->
    rank x = rank y ->
    exists z : G, z \in p /\ rank x < rank z.

Definition x194_treedepth_at_most (G : sgraph) (k : nat) : Prop :=
  exists rank : G -> 'I_k, x194_vertex_ranking rank.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  exists c : nat,
    forall G : sgraph, ~ minor G H -> clustered_colouring G k c.

(** ** X194 statements *****************************************************)

(** Norin-Scott-Seymour-Wood Conjecture 4: the clustered chromatic number of
    the [H]-minor-free class is at most [2*td(H)-2]. *)
(** The [2 <= k] guard is LOAD-BEARING: at treedepth 1 (edgeless H) the bound
    2*k-2 truncates to 0 colours and K_1 (which is H-minor-free for any H with
    >= 2 vertices) refutes the unguarded statement axiom-free; the source's
    domain is H with an edge, i.e. treedepth >= 2 (verify fix 2026-07-18,
    meta/BLOCKED_RETARGETING_AUDIT.md, repaired-rows section). *)
Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      2 <= k ->
      x194_treedepth_at_most H k ->
      x194_clustered_chromatic_minor_class_le H (2 * k - 2).
