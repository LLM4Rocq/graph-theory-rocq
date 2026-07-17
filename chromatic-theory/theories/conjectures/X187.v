(** * Chromatic.conjectures.X187 -- v2 planar request-graph colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X187 vocabulary ***********************************************)

Definition x187_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x187_proper_3_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x187_request_pair (G : sgraph) (r x y : G) : bool :=
  (x != y) && (N(r) == [set x; y]).

Definition x187_request_graph
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat) : Prop :=
  [disjoint ReqEq & ReqNeq] /\
  forall r : G,
    r \in ReqEq :|: ReqNeq -> #|N(r)| = 2 /\ 0 < w r.

Definition x187_eq_request_satisfied
    (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G,
      x187_request_pair r x y && (col x == col y)]].

Definition x187_neq_request_satisfied
    (G : sgraph) (col : G -> 'I_3) (r : G) : bool :=
  [exists x : G, [exists y : G,
      x187_request_pair r x y && (col x != col y)]].

Definition x187_total_request_weight
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat) : nat :=
  \sum_(r in ReqEq) w r + \sum_(r in ReqNeq) w r.

Definition x187_satisfied_request_weight
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat)
    (col : G -> 'I_3) : nat :=
  \sum_(r in ReqEq | x187_eq_request_satisfied col r) w r +
  \sum_(r in ReqNeq | x187_neq_request_satisfied col r) w r.

Definition x187_satisfies_fraction
    (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat)
    (p q : nat) (col : G -> 'I_3) : Prop :=
  p * x187_total_request_weight ReqEq ReqNeq w <=
  q * x187_satisfied_request_weight ReqEq ReqNeq w col.

(** ** X187 statements *****************************************************)

(** Dvorak-Sereni request-graph problem: there is a positive constant [alpha]
    such that every planar triangle-free request graph has a proper 3-colouring
    satisfying at least an [alpha]-fraction of the total request weight.  Positive
    rational weights are encoded by positive natural weights, without loss for
    finite request sets after clearing denominators. *)
Definition planar_triangle_free_request_graph_fraction_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat),
        wagner_planar G ->
        x187_triangle_free G ->
        x187_request_graph ReqEq ReqNeq w ->
        exists col : G -> 'I_3,
          x187_proper_3_colouring col /\
          x187_satisfies_fraction ReqEq ReqNeq w p q col].

