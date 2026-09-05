(** Source-facing finite frozen-colouring bound, for exactly Delta(G)+1
    colours, using the repository's maximum-degree definition. *)
From GTBase Require Import base.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core frozen_coloring_recolor
  frozen_coloring_bound.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_greedy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition fc_delta_palette (G : sgraph) : finType :=
  [the finType of 'I_(Delta G).+1].

Lemma fc_delta_budget (G : sgraph) (x : G) :
  #|fc_closed x| <= #|fc_delta_palette G|.
Proof.
rewrite /fc_delta_palette card_ord /fc_closed cardsU1 in_opn sg_irrefl /= add1n.
rewrite ltnS /Delta.
exact: leq_bigmax.
Qed.

Definition fc_delta_proper_count (G : sgraph) : nat :=
  #|[set f : fc_coloring G (fc_delta_palette G) | fc_proper f]|.
Definition fc_delta_frozen_count (G : sgraph) : nat :=
  #|[set f : fc_coloring G (fc_delta_palette G) | fc_frozen_proper f]|.

Lemma fc_delta_proper_positive (G : sgraph) : 0 < fc_delta_proper_count G.
Proof.
apply/card_gt0P.
have [f proper] := @fc_proper_exists G (fc_delta_palette G)
  (@ord0 (Delta G)) (@fc_delta_budget G).
exists f; by rewrite inE.
Qed.

Theorem fc_delta_frozen_count_bound (G : sgraph) :
  connected [set: G] -> ~ clique [set: G] ->
  (0 < fc_delta_proper_count G) /\
  ((#|G| + 4) * fc_delta_frozen_count G <= 4 * fc_delta_proper_count G).
Proof.
move=> conn nc; split; first exact: fc_delta_proper_positive.
exact (@fc_frozen_count_bound G (fc_delta_palette G) (@fc_delta_budget G) conn nc).
Qed.

Theorem fc_delta_frozen_count_quantitative (G : sgraph) :
  connected [set: G] -> ~ clique [set: G] ->
  forall k, 4 * k <= #|G| ->
    k * fc_delta_frozen_count G <= fc_delta_proper_count G.
Proof.
move=> conn nc k kn.
exact (@fc_frozen_count_quantitative G (fc_delta_palette G)
  (@fc_delta_budget G) conn nc k kn).
Qed.

Definition fc_delta_isolated_count (G : sgraph) : nat :=
  #|[set f : fc_coloring G (fc_delta_palette G) |
    fc_proper f && fc_isolated f]|.

Lemma fc_delta_frozen_isolated_count (G : sgraph) :
  fc_delta_frozen_count G = fc_delta_isolated_count G.
Proof.
rewrite /fc_delta_frozen_count /fc_delta_isolated_count.
apply: eq_card=> f; rewrite !inE /fc_frozen_proper.
case proper: (fc_proper f)=> //=.
exact: fc_frozen_isolated_iff proper.
Qed.

Theorem fc_delta_isolated_count_bound (G : sgraph) :
  connected [set: G] -> ~ clique [set: G] ->
  (0 < fc_delta_proper_count G) /\
  ((#|G| + 4) * fc_delta_isolated_count G <= 4 * fc_delta_proper_count G).
Proof.
move=> conn nc; rewrite -fc_delta_frozen_isolated_count.
exact: fc_delta_frozen_count_bound conn nc.
Qed.

Print Assumptions fc_delta_frozen_count_bound.
Print Assumptions fc_delta_frozen_count_quantitative.
Print Assumptions fc_delta_isolated_count_bound.
