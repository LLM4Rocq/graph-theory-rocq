(** * GTMisc.conjectures.X40 -- v2 coarse Menger c=2 row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X39.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X40 statements ******************************************************)

(** arXiv:2508.14332, Conjecture 1.1 at c = 2. *)
Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          x39_separates_xy S T (x39_set_ball ell X).
