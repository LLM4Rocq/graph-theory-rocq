(** * GTMisc.conjectures.X80 -- v2 toroidal cop-number row *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X80 vocabulary ************************************************)

Definition x80_legal_move (G : sgraph) (x y : G) : bool :=
  (x == y) || (x -- y).

Definition x80_cop_positions (G : sgraph) (k : nat) := {ffun 'I_k -> G}.

Definition x80_captured
    (G : sgraph) (k : nat) (c : x80_cop_positions G k) (r : G) : bool :=
  [exists i : 'I_k, c i == r].

Definition x80_cops_move
    (G : sgraph) (k : nat)
    (c c' : x80_cop_positions G k) : Prop :=
  forall i : 'I_k, x80_legal_move (c i) (c' i).

Definition x80_cop_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists (c0 : x80_cop_positions G k)
         (strat : x80_cop_positions G k -> G -> x80_cop_positions G k)
         (W : {set (x80_cop_positions G k * G)})
         (rank : x80_cop_positions G k * G -> nat),
    (forall r : G, x80_captured c0 r \/ (c0, r) \in W) /\
    forall (c : x80_cop_positions G k) (r : G),
      (c, r) \in W ->
      ~~ x80_captured c r ->
      let c' := strat c r in
      x80_cops_move c c' /\
      forall r' : G,
        x80_legal_move r r' ->
        x80_captured c' r' \/
        ((c', r') \in W /\ rank (c', r') < rank (c, r)).

(** ** X80 statements ******************************************************)

(** Studies slice: Andreae-Schroeder toroidal cop-number conjecture.  The
    topological foundation's orientable torus predicate is exact on connected
    graph embeddings, so the standard connected-graph cop-number convention is
    carried explicitly. *)
Definition toroidal_graph_cop_number_three_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    toroidal G ->
    x80_cop_number_at_most G 3.
