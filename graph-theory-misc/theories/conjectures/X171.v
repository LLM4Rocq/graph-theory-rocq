(** * GTMisc.conjectures.X171 -- v2 Chen-Chvatal graph-metric finite exceptions row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X171 vocabulary ***********************************************)

(** The Chen-Chvatal metric-line/bridge lower bound [ell(G) + br(G) >= |G|]. *)
Definition x171_metric_lines_bridges_bound (G : sgraph) : Prop :=
  #|G| <= metric_line_count G + bridge_count G.

Definition x171_has_pendant_edge (G : sgraph) : Prop :=
  exists v : G, #|N(v)| = 1.

(** ** X171 statements *****************************************************)

(** Aboulker-Matamala-Rochet-Zamora Conjecture 2.2: there is a finite set [F0]
    such that every connected graph outside [F0] either has a pendant edge or
    satisfies [ell(G) + br(G) >= |G|].  The finite exceptional family is encoded
    by an order bound: all larger connected graphs must satisfy the dichotomy. *)
Definition finite_exception_pendant_or_metric_lines_bridges_statement : Prop :=
  exists exceptional_order_bound : nat,
    forall G : sgraph,
      connected [set: G] ->
      exceptional_order_bound < #|G| ->
      x171_has_pendant_edge G \/ x171_metric_lines_bridges_bound G.
