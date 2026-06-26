(** * Digraph.coverage — every 5 cells contain an obstruction

    Paper §5.4(b): every 5-subset of the 8 cells contains one of the 20
    obstruction sets — equivalently, any occupancy pattern avoiding all 20
    obstructions covers at most 4 cells. This is the one purely
    combinatorial, n-independent step of the development (Decision D6): it
    is proved by exhaustive boolean case analysis — 256 cases, each closed
    by computation. (The abstract ω̄ does not compute — mathcomp's [enum] is
    locked — so the computation happens on this purpose-built boolean
    statement instead, exactly as planned.) *)

From mathcomp Require Import all_boot.
From Digraph Require Import obstructions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma coverage5 (b0 b1 b2 b3 b4 b5 b6 b7 : bool) :
  ~~ obstrb b0 b1 b2 b3 b4 b5 b6 b7 ->
  (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 <= 4)%N.
Proof.
by case: b0; case: b1; case: b2; case: b3;
   case: b4; case: b5; case: b6; case: b7.
Qed.
