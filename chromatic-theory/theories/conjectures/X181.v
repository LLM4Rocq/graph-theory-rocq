(** * Chromatic.conjectures.X181 -- v2 random clique-colouring constant row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X181 vocabulary ***********************************************)

Definition x181_monochromatic
    (G : sgraph) (k : nat) (col : G -> 'I_k) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, col x == col y]].

Definition x181_maximal_clique (G : sgraph) (S : {set G}) : bool :=
  [&& 1 < #|S|, cliqueb S
    & [forall T : {set G}, (S \proper T) ==> ~~ cliqueb T]].

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      x181_maximal_clique S ==> ~~ x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (x181_clique_chromatic_window a b).

(** ** X181 statements *****************************************************)

(** Alon-Krivelevich: [chi_c(G(n,1/2)) = (1/2+o(1)) log n] with high
    probability, using exact labelled [G(n,1/2)] counting and rational epsilon
    windows around [log_2 n / 2]. *)
Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  x181_random_graph_clique_chromatic_constant.
