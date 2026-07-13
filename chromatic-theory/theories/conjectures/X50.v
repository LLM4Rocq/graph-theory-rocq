(** * Chromatic.conjectures.X50 -- v2 same-girth induced-free row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X50 vocabulary ************************************************)

Definition x50_same_girth (G H : sgraph) : Prop :=
  forall g : nat, has_girth G g <-> has_girth H g.

Definition x50_induced_F_free (F G : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ F).

Definition x50_all_F_free_induced_subgraphs_c_colourable
    (F G : sgraph) (c : nat) : Prop :=
  forall S : {set G},
    x50_induced_F_free F (induced S) ->
    χ([set: induced S]) <= c.

(** ** X50 statements ******************************************************)

(** arXiv:2203.03612, high-chromatic graphs with same girth and bounded
    F-free induced subgraphs. *)
Definition triangle_free_same_girth_high_chromatic_induced_free_statement : Prop :=
  forall F : sgraph,
    triangle_free F ->
    (exists g : nat, has_girth F g) ->
    exists cF : nat,
      forall target : nat,
        exists G : sgraph,
          target <= χ([set: G]) /\
          x50_same_girth F G /\
          x50_all_F_free_induced_subgraphs_c_colourable F G cF.
