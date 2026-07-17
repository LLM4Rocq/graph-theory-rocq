(** * Packing.conjectures.X178 -- v2 Gallai odd-semiclique path row *)

From GTBase Require Export base.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X178 vocabulary ***********************************************)

Definition x178_path_seq (G : sgraph) (p : seq G) : Prop :=
  (p != [::]) /\ uniq p /\ sorted (--) p.

Definition x178_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
    [exists x : G, [exists y : G,
      [&& x -- y, e == [set x; y], x \in p, y \in p & @consec G p x y]]]].

Definition x178_path_decomposition_at_most (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, x178_path_seq (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint x178_path_edge_set (P i) & x178_path_edge_set (P j)])
      & \bigcup_(i : 'I_r) x178_path_edge_set (P i) = edge_setG G].

Definition x178_missing_edges (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && ~~ cliqueb e].

Definition x178_odd_semi_clique (G : sgraph) : Prop :=
  exists k : nat,
    [/\ 1 <= k, #|G| = 2 * k + 1 & #|x178_missing_edges G| <= k.-1].

(** ** X178 statements *****************************************************)

(** Bonamy-Perrett question: every connected graph that is not an odd
    semi-clique admits an edge-decomposition into at most floor(|V(G)|/2) paths.
    Odd semi-cliques are encoded as graphs on [2k+1] vertices obtained from a
    clique by deleting at most [k-1] edges. *)
Definition gallai_odd_semiclique_path_decomposition_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    ~ x178_odd_semi_clique G ->
    x178_path_decomposition_at_most G (#|G| %/ 2).

