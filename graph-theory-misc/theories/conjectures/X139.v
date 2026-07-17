(** * GTMisc.conjectures.X139 -- v2 polynomial-expansion/scol row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X139 vocabulary ***********************************************)

Fixpoint x139_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x139_poly_eval q x else 0.

Definition x139_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x139_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, x139_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x139_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x139_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> x139_grad_at_most G r (x139_poly_eval p r).

Definition x139_ordering (G : sgraph) (ord : G -> nat) : Prop := injective ord.

Definition x139_strong_reach_set
    (G : sgraph) (ord : G -> nat) (r : nat) (v : G) : {set G} :=
  [set u : G | (@graph_dist G v u <= r) && (ord u <= ord v)].

Definition x139_scol_at_most (G : sgraph) (r k : nat) : Prop :=
  exists ord : G -> nat,
    x139_ordering ord /\
    forall v : G, #|x139_strong_reach_set ord r v| <= k.

(** ** X139 statements *****************************************************)

(** Esperet-Raymond: every graph class with polynomial expansion has polynomially
    bounded strong colouring numbers. *)
Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).
