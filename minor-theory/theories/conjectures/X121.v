(** * Minor.conjectures.X121 -- v2 (tw,ω)-bounded ↔ bounded tree-α row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X121 vocabulary ***********************************************)

(** Clique number ω(G): the size of a largest clique, taken over the whole
    vertex set [set: G].  [ω(A)] is the corpus (coq-graph-theory) clique number
    of the subgraph induced on [A]. *)
Definition x121_omega (G : sgraph) : nat := ω([set: G]).

(** Tree-independence-number bound.  [x121_tree_alpha_le G k] holds iff G admits
    a valid tree-decomposition all of whose bags [B] satisfy α(G[B]) ≤ k, where
    [α(bag t)] is the independence number of the subgraph of G induced on the
    bag [bag t] — i.e. a maximum stable subset of [bag t] under G's adjacency.

    The tree-independence number tree-α(G) is the MIN over tree-decompositions T
    of the MAX over bags B of α(G[B]); "tree-α(G) ≤ k" is exactly the existence
    of one tree-decomposition whose every bag has α ≤ k, which is the clean
    corpus encoding (identical to GTMisc.X102's [x102_tree_alpha_at_most]) and
    avoids a literal minimum. *)
Definition x121_tree_alpha_le (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x27_tree_decomposition bag /\
    forall t : T, α(bag t) <= k.

(** ** X121 statements *****************************************************)

(** Dallard–Milanič–Štorgel.  A class C of graphs is (tw,ω)-BOUNDED — treewidth
    is bounded by some function of the clique number ω throughout C — if and only
    if C has BOUNDED tree-independence number (bounded tree-α).

    "(tw,ω)-bounded"  ≡  ∃ f, ∀ G ∈ C, tw(G) ≤ f(ω(G));
    "bounded tree-α"  ≡  ∃ k, ∀ G ∈ C, tree-α(G) ≤ k.

    Both sides are ∃-witness-BEFORE-∀-G ("there is one f / one k that works for
    every graph in the class"), and the theorem is the biconditional over ALL
    classes C : sgraph -> Prop.  Treewidth is the corpus predicate
    [x27_treewidth_at_most G m] (= tw(G) ≤ m). *)
Definition dallard_milanic_storgel_tw_omega_tree_alpha_statement : Prop :=
  forall C : sgraph -> Prop,
    (exists f : nat -> nat,
       forall G : sgraph, C G -> x27_treewidth_at_most G (f (x121_omega G)))
    <->
    (exists k : nat,
       forall G : sgraph, C G -> x121_tree_alpha_le G k).
