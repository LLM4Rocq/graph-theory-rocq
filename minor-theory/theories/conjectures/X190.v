(** * Minor.conjectures.X190 -- v2 thin overlay without bounded degree row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X190 vocabulary ***********************************************)

Definition x190_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x190_strongly_sublinear_separator_class (C : sgraph -> Prop) : Prop :=
  exists a b K : nat,
    0 < a /\ a < b /\
    forall (G : sgraph) (rho : G -> nat),
      C G ->
      exists S : {set G},
        (#|S| ^ b <= K * (#|G|.+1 ^ a)) /\
        forall A : {set G},
          A \subset ~: S ->
          connected A ->
          2 * x190_weight rho A <= x190_weight rho [set: G].

Record x190_overlay (G : sgraph) (thin : nat) := {
  x190_cover_graph : sgraph;
  x190_cover_map : x190_cover_graph -> G;
  x190_fibre_thin : forall v : G, #|[set x : x190_cover_graph | x190_cover_map x == v]| <= thin;
  x190_edge_lift :
    forall u v : G, u -- v ->
      exists x y : x190_cover_graph,
        [/\ x190_cover_map x = u, x190_cover_map y = v & x -- y]
}.

Definition x190_thin_system_of_overlays (C : sgraph -> Prop) : Prop :=
  exists thin : nat,
    forall G : sgraph, C G -> exists _ : x190_overlay G thin, True.

(** ** X190 statements *****************************************************)

(** Dvorak informal conjecture: the bounded-maximum-degree assumption in the
    thin-overlay theorem can be dropped. *)
Definition thin_overlay_without_bounded_degree_statement : Prop :=
  forall C : sgraph -> Prop,
    x190_strongly_sublinear_separator_class C ->
    x190_thin_system_of_overlays C.
