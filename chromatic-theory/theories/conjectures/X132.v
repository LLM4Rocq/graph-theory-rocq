(** * Chromatic.conjectures.X132 -- v2 planar list-flexibility row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X132 vocabulary ***********************************************)

(** Triangle-free, for simple graphs, is represented by girth at least four. *)
Definition x132_triangle_free (G : sgraph) : Prop := girth_geq G 4.

(** ** X132 statements *****************************************************)

(** Dvorak-Norin-Postle flexibility conjecture: there is an epsilon > 0 such
    that every planar graph is weighted epsilon-flexible for list sizes five in
    general, four in the triangle-free case, and three in the girth-at-least-five
    case. *)
Definition dvorak_norin_postle_planar_list_flexibility_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall G : sgraph,
        wagner_planar G ->
        weighted_epsilon_flexible G 5 p q /\
        (x132_triangle_free G -> weighted_epsilon_flexible G 4 p q) /\
        (girth_geq G 5 -> weighted_epsilon_flexible G 3 p q)].
