(** * Chromatic.conjectures.X31 -- v2 chromatic-girth subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X31 vocabulary ************************************************)

Definition x31_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

(** ** X31 statements ******************************************************)

(** arXiv:1808.01605, high chromatic number forces high-girth, high-average-
    degree subgraphs. *)
Definition chromatic_girth_average_degree_subgraph_statement : Prop :=
  forall k g : nat,
    0 < k ->
    3 <= g ->
    exists c : nat,
      0 < c /\
      forall G : sgraph,
        c <= χ([set: G]) ->
        exists H : sgraph,
          x31_subgraph_of H G /\
          girth_geq H g /\
          average_degree_geq H k 1.
