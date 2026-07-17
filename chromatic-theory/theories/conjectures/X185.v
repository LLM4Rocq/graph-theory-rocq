(** * Chromatic.conjectures.X185 -- v2 widespread multigraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X185 vocabulary ***********************************************)

Definition x185_contains_induced_long_subdivision
    (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

Definition x185_widespread (H : mgraph) : Prop :=
  forall nu ell : nat,
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        x185_contains_induced_long_subdivision G (line_graph H) ell.

(** ** X185 statements *****************************************************)

(** Scott-Seymour Conjecture 1.8: every loopless multigraph is widespread.  The
    multigraph target is represented through its line graph, with widespreadness
    stated as the usual large-chromatic induced-subdivision forcing property. *)
Definition every_multigraph_widespread_statement : Prop :=
  forall H : mgraph, loopless H -> x185_widespread H.
