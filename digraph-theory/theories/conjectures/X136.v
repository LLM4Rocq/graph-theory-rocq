(** * Digraph.conjectures.X136 -- v2 tournament Erdos-Hajnal row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament.
From Digraph.conjectures Require Import heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Erdos-Hajnal for tournaments: every forbidden tournament [H] has a positive
    exponent tau such that every induced-H-free tournament [G] contains a
    transitive subtournament of size at least |G|^tau.  The exponent is a
    positive rational [a/b], encoded by [|G|^a <= |S|^b]. *)
Definition erdos_hajnal_tournament_transitive_subtournament_statement : Prop :=
  forall H : tournament,
    exists a b : nat,
      [/\ 0 < a, 0 < b &
        forall G : tournament,
          ind_free (H : diGraphType) (G : diGraphType) ->
          exists S : {set G},
            #|G| ^ a <= #|S| ^ b /\
            transb (sub_tournament S)].

