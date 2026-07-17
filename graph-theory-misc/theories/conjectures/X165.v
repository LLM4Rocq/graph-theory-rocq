(** * GTMisc.conjectures.X165 -- v2 Szeged-Wiener difference row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X165 vocabulary ***********************************************)

Definition x165_wiener_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G) graph_dist u v) %/ 2.

Definition x165_closer_count (G : sgraph) (u v : G) : nat :=
  #|[set x : G | graph_dist x u < graph_dist x v]|.

Definition x165_szeged_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G | u -- v)
      x165_closer_count u v * x165_closer_count v u) %/ 2.

Definition x165_eta (G : sgraph) : nat :=
  x165_szeged_index G - x165_wiener_index G.

Definition x165_K_n_t (G : sgraph) (n t : nat) : Prop :=
  #|G| = n /\
  exists apex : G,
    #|N(apex)| = t /\ cliqueb (~: [set apex]).

Definition x165_exceptional_family (G : sgraph) (n : nat) : Prop :=
  inhabited (G ≃ 'K_n) \/
  x165_K_n_t G n 2 \/
  x165_K_n_t G n (n - 2).

(** ** X165 statements *****************************************************)

(** Conjecture 5: every 2-connected n-vertex graph, n>=10, except K_n and two
    paper-local exceptional families, satisfies eta(G)>=2n. *)
Definition szeged_wiener_difference_exceptional_graphs_statement : Prop :=
  forall (n : nat) (G : sgraph),
    10 <= n ->
    #|G| = n ->
    k_connected G 2 ->
    ~ x165_exceptional_family G n ->
    2 * n <= x165_eta G.
