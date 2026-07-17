(** * Extremal.conjectures.X195 -- v2 Ramsey-nice eventual row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X195 vocabulary ***********************************************)

Definition x195_contains_forest (k : nat) (Fam : 'I_k -> sgraph) : Prop :=
  exists i : 'I_k, is_forest [set: Fam i].

Definition x195_monochromatic_copy
    (Host F : sgraph) (colour : {set Host} -> 'I_2) (target : 'I_2) : Prop :=
  exists emb : F -> Host,
    injective emb /\
    (forall x y : F, x -- y -> emb x -- emb y) /\
    forall x y : F, x -- y -> colour [set emb x; emb y] = target.

Definition x195_k_nice (r k : nat) (Fam : 'I_r -> sgraph) : Prop :=
  exists N : nat,
    forall colour : {set 'K_N} -> 'I_2,
      exists i : 'I_r,
        @x195_monochromatic_copy 'K_N (Fam i) colour (inord (val i %% 2)).

(** ** X195 statements *****************************************************)

(** Aharoni-Alon-Amir-Haxell-Hefetz-Jiang-Kronenberg-Naor Question 1.1:
    every finite graph family containing a forest should be eventually
    [k]-nice. *)

Definition ramsey_nice_forest_family_eventual_statement : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    0 < r ->
    x195_contains_forest Fam ->
    exists k0 : nat,
      forall k : nat, k0 <= k -> x195_k_nice k Fam.
