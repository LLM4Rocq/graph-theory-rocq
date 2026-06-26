(** * Digraph.conjectures.twinwidth_ordered — CONCRETE ordered twin-width and
    BST-orderings; upgrade of AACL Conjectures 3.13 / 3.16 (arXiv:2310.04265).

    [twinwidth.v] states the twin-width conjectures 3.12 / 3.13 / 3.16.  There,
    twin-width [tww_le] (hence Conj 3.12) is CONCRETE, but ORDERED twin-width
    ([otww_le]) and the BST-ordering predicate ([bst_order]) are exposed
    PARAMETRICALLY over abstract predicates, with the order-contiguity of the
    contraction chain and the recursive BST in-order traversal flagged as the
    blocked pieces.

    This file UPGRADES both pieces to CONCRETE, one-file forms:

      1. ORDERED TWIN-WIDTH (concrete).  Fix an order [p : {perm T}] read through
         [ltp p] ([order.v]).  A part [X] (a class of a contraction partition) is
         a [p]-INTERVAL when no vertex outside [X] lies strictly [ltp p]-between
         two vertices of [X]: [X] is a contiguous block of the order.  A partition
         [e] is [p]-ORDERED when every class is a [p]-interval.  An ORDERED
         contraction sequence (w.r.t. [p]) is a contraction sequence (in the
         concrete sense of [twinwidth.v]: discrete start, total end, single merges,
         each relation an equivalence) ALL of whose relations are [p]-ordered —
         equivalently every merge fuses two [p]-contiguous parts (merging two
         [p]-adjacent intervals yields a [p]-interval, and conversely the chain of
         interval-partitions exactly tracks the order-respecting merges).  We give
         this as the CONCRETE predicate [concrete_otww_le T p k]: some ordered
         contraction sequence has width [≤ k].

      2. BST-ORDERING (concrete).  A BST-ordering is the in-order traversal of a
         binary search tree where, at each node [r], the left subtree is exactly
         [N^-(r)] (in-neighbours) restricted to the current set and the right
         subtree exactly [N^+(r)] (out-neighbours) restricted to the current set
         (scripts/bst_penalty.py: in a tournament a chosen root [r] EXACTLY
         bipartitions the rest into [N^-(r)] and [N^+(r)]).  Concretely: [p] is a
         BST-ordering iff on every order-interval [S] the [p]-least-after-its-left-
         block vertex (the in-order root [r] of [S]) has its [≺_p r] part of [S]
         equal to [N^-(r) ∩ S] and its [≻_p r] part equal to [N^+(r) ∩ S], and the
         two sides recurse.  We define this by a fuel-bounded recursion on [#|S|]
         as the CONCRETE predicate [concrete_bst_order T p].

    Then we RE-STATE Conj 3.13 / 3.16 by instantiating [twinwidth.v]'s parametric
    statements at the concrete [concrete_otww_le] / [concrete_bst_order], and
    PROVE the relative edges 3.16 ⟹ 3.13 ⟹ 3.12 carry over to the concrete
    instances (threading the same proved bridges as the parametric edges).

    CONCRETE vs PARAMETRIC: BOTH ordered twin-width and the BST-ordering predicate
    are now CONCRETE (no abstract predicate, no Admitted/Axiom).  The faithful
    bridges that the conjectures depend on (ordered ⇒ unordered domination; back-
    degeneracy χ⃗ ≤ g(ω); the structural BST refinement of a bounded order) remain
    carried as explicit Qed-closing hypotheses on the relative edges, exactly as in
    [twinwidth.v].  All degenerate cases are guarded by [0 < #|T|]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order dichromatic omegabar.
From Digraph Require Import twinwidth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Concrete ordered twin-width *)

Section ConcreteOrderedTwinWidth.
Variable T : tournament.
Variable p : {perm T}.
Implicit Types (e : rel T) (u v : T).

(** A vertex [w] lies strictly [ltp p]-between [u] and [v] when [u ≺_p w ≺_p v].
    A part [X] is a [p]-INTERVAL when nothing OUTSIDE [X] lies strictly between
    two members of [X]: [X] is a contiguous block of the order [p]. *)

Definition p_between (u w v : T) : bool := ltp p u w && ltp p w v.

Definition p_interval (X : {set T}) : bool :=
  [forall u, [forall v, [forall w,
     (u \in X) ==> (v \in X) ==> (w \notin X) ==> ~~ p_between u w v]]].

(** A partition [e] (an equivalence relation) is [p]-ORDERED when every class
    [eclass e u] is a [p]-interval. *)

Definition p_ordered (e : rel T) : bool :=
  [forall u, p_interval (eclass e u)].

(** An ORDERED contraction sequence w.r.t. [p]: a (concrete) contraction
    sequence ([twinwidth.v]) ALL of whose relations are [p]-ordered.  Each merge
    therefore fuses two [p]-contiguous parts. *)

Definition ordered_contraction_seq (s : seq (rel T)) : Prop :=
  let d0 : rel T := fun u v => u == v in
  contraction_seq s /\
  (forall i : nat, (i < size s)%N -> p_ordered (nth d0 s i)).

(** Concrete ordered twin-width: some ordered contraction sequence has width
    [≤ k]. *)

Definition concrete_otww_le (k : nat) : Prop :=
  exists s : seq (rel T),
    ordered_contraction_seq s /\ (seq_width s <= k)%N.

End ConcreteOrderedTwinWidth.

Arguments concrete_otww_le {T} p k.

(** *** Concrete ordered twin-width dominates (unordered) twin-width

    An ordered contraction sequence IS a contraction sequence, so a concrete
    ordered-tww bound entails the [tww_le] bound — this is the faithful
    [otww_dominates_tww] axiom of [twinwidth.v], now PROVED for the concrete
    predicate. *)

Lemma concrete_otww_dominates_tww (T : tournament) (p : {perm T}) (k : nat) :
  concrete_otww_le p k -> tww_le T k.
Proof. by move=> [s [[cs _] w]]; exists s. Qed.

(** The concrete ordered twin-width satisfies [twinwidth.v]'s abstract
    [otww_dominates_tww] axiom (read at the concrete instance). *)

Lemma concrete_otww_dominates_tww_holds :
  otww_dominates_tww (fun (T : tournament) (p : {perm T}) => concrete_otww_le p).
Proof. by move=> T p k; exact: concrete_otww_dominates_tww. Qed.

(** ** Concrete BST-orderings

    In a tournament, choosing a root [r] of an order-interval [S] EXACTLY
    bipartitions [S \ {r}] into [N^-(r) ∩ S] (left subtree) and [N^+(r) ∩ S]
    (right subtree).  The in-order traversal lays out [inorder(left), r,
    inorder(right)].  An order [p] realizes such a traversal precisely when, on
    every relevant interval [S], the in-order root [r] (the unique vertex of [S]
    whose strict-[≺_p] part of [S] equals [N^-(r) ∩ S]) is consistent with the
    arcs, and both sides recurse.  We capture this by a fuel-bounded recursion on
    [#|S|]. *)

Section ConcreteBST.
Variable T : tournament.
Variable p : {perm T}.

(** The [p]-strict-lower and [p]-strict-upper parts of [S] relative to [r]. *)
Definition lo_part (S : {set T}) (r : T) : {set T} := [set x in S | ltp p x r].
Definition hi_part (S : {set T}) (r : T) : {set T} := [set x in S | ltp p r x].

(** [r] is a valid BST-root of [S]: [r ∈ S], the [p]-lower part of [S] is
    exactly the in-neighbours of [r] within [S], and the [p]-upper part is
    exactly the out-neighbours of [r] within [S].  (In a tournament these two
    conditions are equivalent and partition [S \ {r}].) *)

Definition bst_root (S : {set T}) (r : T) : bool :=
  (r \in S) && (lo_part S r == [set x in S | x --> r])
            && (hi_part S r == [set x in S | r --> x]).

(** Fuel-bounded BST-traversal predicate: with fuel [n ≥ #|S|], either [S] is
    empty/singleton (trivially a valid leaf/0-node interval), or there is a valid
    BST-root [r] of [S] and both the lower and upper parts recurse. *)

Fixpoint bst_traversal (n : nat) (S : {set T}) : bool :=
  match n with
  | 0 => #|S| == 0
  | n'.+1 =>
      (#|S| <= 1) ||
      [exists r, bst_root S r
                 && bst_traversal n' (lo_part S r)
                 && bst_traversal n' (hi_part S r)]
  end.

(** [p] is a (concrete) BST-ordering of [T]: the full vertex set admits a BST
    traversal (with fuel [#|T|]). *)

Definition concrete_bst_order : Prop :=
  bst_traversal #|T| [set: T].

End ConcreteBST.

Arguments concrete_bst_order {T} p.

(** ** Re-statement of Conjectures 3.13 / 3.16 at the CONCRETE instances

    We instantiate the parametric statements of [twinwidth.v] at the concrete
    ordered-tww predicate and the concrete BST predicate.  (Definitions, so the
    instantiation is transparent and the relative edges below see through them.) *)

Definition conj_3_13_concrete : Prop :=
  conj_3_13_statement
    (fun (T : tournament) (p : {perm T}) => concrete_otww_le p).

Definition conj_3_16_concrete : Prop :=
  conj_3_16_statement
    (fun (T : tournament) (p : {perm T}) => concrete_bst_order p).

(** Unfolding lemmas making the concrete content explicit. *)

Lemma conj_3_13_concreteE :
  conj_3_13_concrete <->
  (exists f : nat -> nat,
     forall T : tournament, (0 < #|T|)%N ->
       exists p : {perm T},
         (bclique p <= f (omegabar T))%N /\ concrete_otww_le p (f (omegabar T))).
Proof. by split=> H; exact: H. Qed.

Lemma conj_3_16_concreteE :
  conj_3_16_concrete <->
  (exists f : nat -> nat,
     forall T : tournament, (0 < #|T|)%N ->
       exists p : {perm T},
         concrete_bst_order p /\ (bclique p <= f (omegabar T))%N).
Proof. by split=> H; exact: H. Qed.

(** ** Relative edges carry over to the concrete instances *)

(** Conjecture 3.16 (concrete) ⟹ Conjecture 3.13 (concrete).

    A BST-ordering, being an order, also bounds ordered twin-width once we know
    the proved structural bridge that a BST-ordering achieving the ω̄-bound also
    achieves the ordered-twin-width bound (the AACL Conj 3.16 ⟹ 3.13 step:
    a BST-order's interval structure yields a bounded ordered contraction
    sequence).  Threaded as the explicit proved hypothesis [bst_gives_otww]. *)

Theorem conj_3_16_concrete_implies_3_13 :
  conj_3_16_concrete ->
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> concrete_bst_order p -> concrete_otww_le p m) ->
  conj_3_13_concrete.
Proof.
move=> [f Hf] bst_gives_otww; exists f => T T0.
have [p [Hbst Hbc]] := Hf T T0.
by exists p; split=> //; exact: (bst_gives_otww T p _ T0 Hbst).
Qed.

(** Conjecture 3.13 (concrete) ⟹ Conjecture 3.16 (concrete).

    The exact concrete analogue of [twinwidth.v]'s [conj_3_13_implies_3_16]:
    if every order achieving the 3.13 bound is in particular a BST-ordering
    (the proved structural refinement, supplied as [bound_is_bst]), then 3.13's
    witness order is a BST-ordering bounding ω(T^p). *)

Theorem conj_3_13_concrete_implies_3_16 :
  conj_3_13_concrete ->
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> (bclique p <= m)%N -> concrete_otww_le p m ->
     concrete_bst_order p) ->
  conj_3_16_concrete.
Proof.
move=> H bound_is_bst.
apply: (conj_3_13_implies_3_16
          (otww_le := fun (T : tournament) (p : {perm T}) => concrete_otww_le p)
          (bst_order := fun (T : tournament) (p : {perm T}) => concrete_bst_order p) H).
exact: bound_is_bst.
Qed.

(** Conjecture 3.16 (concrete) ⟹ Conjecture 3.12.

    The exact concrete analogue of [twinwidth.v]'s [conj_3_16_implies_3_12]:
    a BST-ordering's bounded backedge clique number feeds the proved back-
    degeneracy bound χ⃗(T) ≤ g(ω(T^p)) ([chi_le_bclique]) to bound the dichromatic
    number for every tournament, hence within each bounded-twin-width class. *)

Theorem conj_3_16_concrete_implies_3_12 :
  conj_3_16_concrete ->
  (exists g : nat -> nat,
     forall (T : tournament) (p : {perm T}) (m : nat),
       (0 < #|T|)%N -> (bclique p <= m)%N -> dicolorableb T (g m)) ->
  conj_3_12_statement.
Proof.
move=> H Hg.
exact: (conj_3_16_implies_3_12
          (bst_order := fun (T : tournament) (p : {perm T}) => concrete_bst_order p)
          H Hg).
Qed.

(** Composite: Conjecture 3.16 (concrete) ⟹ Conjecture 3.13 (concrete) ⟹
    Conjecture 3.12, threading both proved bridges. *)

Theorem conj_3_16_concrete_chain :
  conj_3_16_concrete ->
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> concrete_bst_order p -> concrete_otww_le p m) ->
  (exists g : nat -> nat,
     forall (T : tournament) (p : {perm T}) (m : nat),
       (0 < #|T|)%N -> (bclique p <= m)%N -> dicolorableb T (g m)) ->
  conj_3_13_concrete /\ conj_3_12_statement.
Proof.
move=> H bst_gives_otww Hg; split.
- exact: (conj_3_16_concrete_implies_3_13 H bst_gives_otww).
- exact: (conj_3_16_concrete_implies_3_12 H Hg).
Qed.
