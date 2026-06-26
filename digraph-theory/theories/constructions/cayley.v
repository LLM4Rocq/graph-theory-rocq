(** * Digraph.cayley — Cayley digraphs over a finite group

    For a finite group [gT] and a connection set [A : {set gT}], the Cayley
    digraph [cayley A] has the group elements as vertices and an arc
    [x --> y] iff [x^-1 * y \in A].

    Library facts (docs/DESIGN.md §6):
    - [cayley_irreflP] / [cayley_totalP]: [cayley A] is a tournament exactly
      when [A] avoids [1] and splits each pair [{z, z^-1}] (z ≠ 1) exactly
      once — i.e. [A ⊎ A^-1 = gT \ {1}];
    - [translation_aut]: left translations are automorphisms;
    - [cayley_vertex_transitive]: hence Cayley digraphs are vertex-transitive.

    'Z_n's canonical group structure is the *additive* one, so circulants
    (constructions/circulant.v) are literally Cayley digraphs over ['Z_n]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.

(** The carrier is the group; the (otherwise unused) connection set [A] is a
    real parameter of the type alias so that distinct connection sets carry
    distinct canonical instances. *)
Definition cayley (gT : finGroupType) (A : {set gT}) : Type := gT.

Section Cayley.
Variables (gT : finGroupType) (A : {set gT}).

HB.instance Definition _ := Finite.on (cayley A).
HB.instance Definition _ :=
  HasArc.Build (cayley A) (fun x y : gT => (x^-1 * y)%g \in A).

Lemma cayley_arcE (x y : cayley A) : (x --> y) = ((x^-1 * y)%g \in A).
Proof. by []. Qed.

(** ** Tournament characterization *)

Lemma cayley_irreflP :
  (forall x : cayley A, (x --> x) = false) <-> (1%g \notin A).
Proof.
split=> [h | /negbTE h x]; last by rewrite cayley_arcE mulVg h.
by rewrite -(mulVg (1%g : gT)) -cayley_arcE h.
Qed.

Lemma cayley_totalP :
  (forall x y : cayley A, (x != y) = (x --> y) (+) (y --> x)) <->
  (forall z : gT, (z != 1%g) = (z \in A) (+) (z^-1 \in A)).
Proof.
split=> h.
- (* instantiate the tournament axiom at (1, z) *)
  move=> z.
  by have := h 1%g z; rewrite !cayley_arcE invg1 mul1g mulg1 eq_sym.
- move=> x y; rewrite !cayley_arcE.
  have := h (x^-1 * y); rewrite invgM invgK => <-.
  by rewrite -(inj_eq (mulgI x^-1)) mulVg eq_sym.
Qed.

(** ** Translations and vertex-transitivity *)

Definition translation (g : gT) : {perm cayley A} := perm (mulgI g).

Lemma translationE g x : translation g x = (g * x)%g.
Proof. by rewrite permE. Qed.

Lemma translation_aut (g : gT) :
  translation g \in dgaut (cayley A : diGraphType).
Proof.
rewrite dgautE; apply/autbP=> u v; rewrite !cayley_arcE !translationE.
by rewrite invgM -mulgA mulKg.
Qed.

Lemma cayley_vertex_transitive : vertex_transitiveb (cayley A : diGraphType).
Proof.
apply/vertex_transitivebP=> u v.
exists (translation (v * u^-1)%g); first exact: translation_aut.
by rewrite translationE mulgVK.
Qed.

End Cayley.

