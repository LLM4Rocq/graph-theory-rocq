(** * Digraph.conjectures.X123 -- v2 directed Gyarfas-Sumner (tournament + forest) row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import chi_bounded dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X123 vocabulary ************************************************)

(** A transitive tournament: a tournament (irreflexive, semicomplete and
    asymmetric — [heroes.is_tournament]) whose arc relation is transitive, i.e.
    the strict order of a linear order (isomorphic to some [TT n]). *)
Definition x123_transitive_tournament (H : diGraphType) : Prop :=
  is_tournament H /\ transitive (arc : rel H).

(** The class forbidding BOTH [H] and [F] as induced subdigraphs, inside the
    oriented graphs — the pair {H,F} is the forbidden set (cf. [X71]'s
    single-forest [x71_oriented_forb_ind]). *)
Definition x123_forb_pair (H F D : diGraphType) : Prop :=
  chi_bounded.oriented_dg D /\ ind_free H D /\ ind_free F D.

(** ** X123 statements ******************************************************)

(** Aboulker–Charbit–Naserasr directed Gyarfas-Sumner: if [H] is a transitive
    tournament and [F] is a directed forest, then {H,F} is χ⃗-finite — the class
    of oriented graphs with no induced copy of [H] and no induced copy of [F]
    has bounded dichromatic number.  DISTINCT from X71, whose forbidden set is
    the single forest [F]; here it is the PAIR {transitive tournament, forest}.
    [F] is guarded oriented + underlying-forest ("directed forest", as in X71);
    [H] transitive-tournament is itself oriented via [is_tournament]. *)
Definition directed_gyarfas_sumner_tournament_forest_statement : Prop :=
  forall H F : diGraphType,
    x123_transitive_tournament H ->
    chi_bounded.oriented_dg F ->
    chi_bounded.oriented_forest F ->
    dichromatic_bounded (x123_forb_pair H F).
