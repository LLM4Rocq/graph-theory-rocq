(** * Spectral.conjectures.X6 -- v2 milestone X6, clean spectral-energy row *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** ** Local spectral vocabulary *******************************************)

Definition x6_splus (R : rcfType) (s : seq R) : R :=
  \sum_(x <- s | 0 < x) x ^+ 2.

Definition x6_sminus (R : rcfType) (s : seq R) : R :=
  \sum_(x <- s | x < 0) x ^+ 2.

(** ** X6 statements *******************************************************)

(** Studies slice: Elphick-Farber-Goldberg-Wocjan s+/s- conjecture. *)
Definition elphick_farber_goldberg_wocjan_splus_sminus_statement : Prop :=
  forall (R : rcfType) (G : sgraph) (n : nat),
    connected [set: G] -> #|G| = n -> (0 < n)%N ->
    forall s : seq R, is_spectrum (adjmx R G) s ->
      (((n.-1)%:R : R) <= @x6_splus R s)%R /\
      (((n.-1)%:R : R) <= @x6_sminus R s)%R.
