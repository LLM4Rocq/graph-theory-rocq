(** * Digraph.conjectures.dichromatic — P2 keystone: the dichromatic number χ⃗

    The dichromatic number (Neumann-Lara) is the central invariant of the heroes /
    Aboulker corpus: χ⃗(D) is the least number of colours partitioning V(D) so that every
    colour class induces an ACYCLIC subdigraph. This file builds the reusable machinery —
    acyclicity, k-dicolourability, and the "χ⃗-bounded over a class" wrapper — that the
    chordal / heroes / twin-width / 2-extremal conjectures all consume. (Those consumer
    conjectures attach in their phases: P6 heroes, P12 twin-width / 2-extremal, and the
    chordal / oriented-triangle-free families once their class predicates land.)
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §2 (P2). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Acyclicity (decidable)

    A finite digraph is acyclic iff it has no directed cycle. Decidable characterization:
    no arc [v --> w] whose head [w] can reach back to [v] under reflexive-transitive
    reachability [connect arc]. (A loop [v --> v] gives [connect arc v v] reflexively; a
    longer dicycle gives a [w] that reaches [v] around the cycle.) The two lemmas below
    validate this against the library's [dicycle]: every directed cycle refutes
    [acyclicb]. *)
Definition acyclicb (D : diGraphType) : bool :=
  [forall v : D, [forall w : D, (v --> w) ==> ~~ connect arc w v]].

(** A loop (length-1 directed cycle) refutes acyclicity. *)
Lemma loop_not_acyclicb (D : diGraphType) (v : D) : v --> v -> ~~ acyclicb D.
Proof.
move=> vv; apply/forallPn; exists v; rewrite negb_forall; apply/existsP; exists v.
by rewrite negb_imply negbK vv connect0.
Qed.

(** Any directed cycle refutes acyclicity — so [acyclicb] is the genuine acyclicity
    predicate (it is [true] exactly when there is no [dicycle]). *)
Lemma dicycle_not_acyclicb (D : diGraphType) (c : seq D) : dicycle c -> ~~ acyclicb D.
Proof.
case: c => [|z t] dc; first by case/and3P: dc.
have zc : z \in z :: t by rewrite inE eqxx.
have [s [ps _ _ lastA _]] := dicycle_unroll dc zc.
apply/forallPn; exists (last z s); rewrite negb_forall; apply/existsP; exists z.
rewrite negb_imply lastA negbK andTb.
case/andP: ps => pp _; apply/connectP; by exists s.
Qed.

(** ** k-dicolourability

    [dicolorableb D k]: V(D) admits a k-colouring whose every colour class induces an
    acyclic subdigraph — i.e. "χ⃗(D) ≤ k". (Stated over the finite function space
    [{ffun D -> 'I_k}] so it is a decidable boolean.) *)
Definition dicolorableb (D : diGraphType) (k : nat) : bool :=
  [exists col : {ffun D -> 'I_k},
     [forall i : 'I_k, acyclicb (induced_digraph [set v | col v == i])]].

(** ** χ⃗-bounded over a class (the heroic / χ-boundedness wrapper)

    A class [C] of digraphs has bounded dichromatic number when a single bound [B]
    dicolours every member. This is exactly the shape of "[C] is χ⃗-bounded" and of a
    forbidden set being "heroic": the boundedness is a nat-level existential (no reals). *)
Definition dichromatic_bounded (C : diGraphType -> Prop) : Prop :=
  exists B : nat, forall D : diGraphType, C D -> dicolorableb D B.
