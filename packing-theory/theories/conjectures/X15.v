(** * Packing.conjectures.X15 -- v2 fair matching representation rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X15 vocabulary ************************************************)

Definition x15_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x15_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x15_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| <= 1.

Definition x15_edge_partition
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G},
      (e \in x15_edge_set G) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

Definition x15_edge_family
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  forall i : 'I_m, E i \subset x15_edge_set G.

(** ** X15 statements ******************************************************)

(** arXiv:1611.03196, Conjecture 1.14. *)
Definition fair_matching_edge_partition_statement : Prop :=
  forall (m : nat) (H : sgraph) (E : 'I_m -> {set {set H}}),
    x15_edge_partition E ->
    exists M : {set {set H}},
      x15_matching M /\
      forall i : 'I_m,
        (#|E i| %/ (Delta H + 2) <= #|M :&: E i|)%N.

(** arXiv:1611.03196, Conjecture 1.15. *)
Definition bipartite_matching_underrepresentation_statement : Prop :=
  forall m : nat, exists c : nat,
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

(** according to https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md *)
Definition bipartite_matching_underrepresentation_llm_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 32 * (m + 1)^3 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).


(** the constant of the first version of foundations/fair_matching.v: one
    halving per pair along a binary mixing tree, then a trimming phase *)
Definition bipartite_matching_underrepresentation_llm2_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= (m + 1)^2 * (16*m + 29) /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

(** what is proved in foundations/fair_matching.v: the constant of the
    synchronized-rounds proof, linear in m — one exact halving per round of a
    balanced mixing of the colour classes, all the pairs of a round split by a
    single necklace splitting.  The three statements above are corollaries. *)
Definition bipartite_matching_underrepresentation_llm3_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 12 * m + 14 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).
