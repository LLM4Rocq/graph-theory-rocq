(** * Digraph.prelude — shared foundations

    Common imports, global options, and a classical-logic baseline for the whole
    library. Every other file should [From Digraph Require Import prelude.] first.

    Design (see docs/DESIGN.md §2): we work classically (mathcomp-classical's
    [boolp]) so statements read like ordinary mathematics — excluded middle,
    propositional and functional extensionality, and choice are available. The
    [classical_sets] layer ([set T] over an arbitrary [T]) is the seam through
    which the finite, combinatorial core will later extend to infinite / arbitrary
    vertex types (Decision D4). The finite workhorse types come from MathComp
    proper ([finType], [{set T}], [{perm T}], ['Z_n], ...). *)

From mathcomp Require Import all_boot.
From mathcomp Require Import boolp classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** ** Smoke checks

    These exercise both layers so a broken toolchain fails fast at [make] time.
    They carry no mathematical content and may be removed once real modules land. *)

(** Classical logic is in scope (derived from [boolp]'s axioms). *)
Lemma prelude_classical (P : Prop) : P \/ ~ P.
Proof. by case: (pselect P); [left | right]. Qed.

(** The classical set layer is in scope. *)
Lemma prelude_set (T : Type) (A : set T) : A `<=` setT.
Proof. by move=> x _. Qed.

(** MathComp's small-scale reflection is in scope. *)
Lemma prelude_ssr (n : nat) : (n <= n)%N.
Proof. by []. Qed.

(** ** General counting

    Partition counting by a bounded nat-valued class function: any finite
    set splits as the sum of its class sizes. (G2 of docs/k34_dossier.md;
    instances: cell occupancy in applications/k5/cells.v, key classes and
    bands in applications/k4/.) *)

Lemma card_classes (T : finType) (K : {set T}) (f : T -> nat) (b : nat) :
  {in K, forall u, (f u < b)%N} ->
  #|K| = (\sum_(i < b) #|[set u in K | f u == i :> nat]|)%N.
Proof.
case: b => [|b] fb.
  case: (set_0Vmem K) => [->|[u uK]]; last by have := fb u uK.
  by rewrite cards0 big_ord0.
rewrite -sum1_card (partition_big (fun u => @inord b (f u)) xpredT) //=.
apply: eq_bigr => i _; rewrite -sum1_card.
apply: eq_bigl => u; rewrite inE.
case uK : (u \in K) => //=.
have fub : (f u < b.+1)%N by apply: fb; rewrite uK.
apply/eqP/eqP => [<-|e]; first by rewrite inordK.
by apply: ord_inj; rewrite inordK // e.
Qed.

(** When the class function is injective on [K] (one element per class at
    most — e.g. [K] a clique and classes backedge-free), the class sizes
    are occupancy booleans. Generalizes the cell-occupancy counting of
    applications/k5/cells.v; used by the k = 4 files. *)

Lemma card_classes_inj (T : finType) (K : {set T}) (f : T -> nat) (b : nat) :
  {in K, forall u, (f u < b)%N} ->
  {in K &, forall u v, f u = f v -> u = v} ->
  #|K| = (\sum_(i < b) [exists u in K, f u == i :> nat])%N.
Proof.
case: b => [|b] fb finj.
  case: (set_0Vmem K) => [->|[u uK]]; last by have := fb u uK.
  by rewrite cards0 big_ord0.
pose g (u : T) : 'I_b.+1 := inord (f u).
have gE u : u \in K -> g u = f u :> nat.
  by move=> uK; rewrite /g inordK ?fb.
have ginj : {in K &, injective g}.
  by move=> u v uK vK e; apply: finj => //; rewrite -(gE u uK) -(gE v vK) e.
rewrite -(card_in_imset ginj).
have -> : #|g @: K| = (\sum_(i < b.+1) (i \in g @: K))%N.
  rewrite -sum1_card big_mkcond /=.
  by apply: eq_bigr => i _; case: (_ \in _).
apply: eq_bigr => i _.
congr nat_of_bool.
apply/imsetP/existsP => [[u uK ->]|[u /andP[uK /eqP e]]].
- by exists u; rewrite uK (gE u uK) eqxx.
- by exists u => //; apply: ord_inj; rewrite (gE u uK) e.
Qed.
