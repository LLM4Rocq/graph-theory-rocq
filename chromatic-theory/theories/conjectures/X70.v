(** * Chromatic.conjectures.X70 -- v2 Scott-Seymour tournament row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X70 vocabulary ************************************************)

Definition x70_graph
    (V : finType) (E : rel V) (Esym : symmetric E) (Eirr : irreflexive E) :
    sgraph :=
  SGraph Esym Eirr.

Definition x70_tournament_rel (V : finType) (T : rel V) : Prop :=
  irreflexive T /\
  forall x y : V, x != y -> T x y = ~~ T y x.

(** ** X70 statements ******************************************************)

(** Studies slice: Scott-Seymour tournament chi-boundedness conjecture. *)
Definition scott_seymour_tournament_outneighbourhood_chi_statement : Prop :=
  forall k : nat,
    exists K : nat,
      forall (V : finType) (T E : rel V)
             (Esym : symmetric E) (Eirr : irreflexive E),
        x70_tournament_rel T ->
        let G := x70_graph Esym Eirr in
        K <= χ([set: G]) ->
        exists v : G,
          k <= χ([set: induced [set u : G | T v u]]).
