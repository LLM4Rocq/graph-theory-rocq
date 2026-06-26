(** * Digraph.product — lexicographic substitution S[H]

    The (uniform) substitution of [H] into every vertex of [S], also called
    the lexicographic product: vertices are pairs [(s, h)], and there is an
    arc [(s1,h1) --> (s2,h2)] iff [s1 --> s2], or [s1 = s2] and [h1 --> h2]
    (paper, "lexicographic substitution"; docs/DESIGN.md §6).

    The carrier is the product type [S * H] with the canonical [Finite]
    structure; the arc relation is declared as a canonical instance on the
    alias [lexprod S H], and the tournament axioms are closed under the
    construction ([S[H]] is a tournament whenever [S] and [H] are — the M2
    exit fact). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LexProd.
Variables D1 D2 : diGraphType.

Definition lexprod : Type := (D1 * D2)%type.

HB.instance Definition _ := Finite.on lexprod.
HB.instance Definition _ := HasArc.Build lexprod
  (fun u v : D1 * D2 => arc u.1 v.1 || (u.1 == v.1) && arc u.2 v.2).

Lemma lexprod_arcE (u v : lexprod) :
  (u --> v) = (u.1 --> v.1) || (u.1 == v.1) && (u.2 --> v.2).
Proof. by []. Qed.

Lemma card_lexprod : #|{: lexprod}| = #|D1| * #|D2|.
Proof. by rewrite card_prod. Qed.

End LexProd.

(** ** Tournament closure: S[H] is a tournament when S and H are *)

Section LexProdTournament.
Variables T1 T2 : tournament.

Fact lexprod_irrefl : irreflexive (arc : rel (lexprod T1 T2)).
Proof.
by move=> [s h]; rewrite lexprod_arcE /= !arcxx eqxx.
Qed.

Fact lexprod_total (u v : lexprod T1 T2) :
  (u != v) = (arc u v) (+) (arc v u).
Proof.
case: u v => [s1 h1] [s2 h2]; rewrite !lexprod_arcE /= xpair_eqE negb_and.
case: (eqVneq s1 s2) => [->|sDs] /=.
- by rewrite arcxx /= arc_total.
- by rewrite !orbF -arc_total sDs.
Qed.

HB.instance Definition _ :=
  DiGraph_IsTournament.Build (lexprod T1 T2) lexprod_irrefl lexprod_total.

End LexProdTournament.

(** Object-level version for statements. *)
Definition lexprod_tournament (T1 T2 : tournament) : tournament :=
  lexprod T1 T2 : tournament.

(** ** Vertex-transitivity is preserved by lexicographic product *)

Section LexProdVT.
Variables D1 D2 : diGraphType.

Lemma lexprod_vertex_transitive :
  vertex_transitiveb D1 -> vertex_transitiveb D2 ->
  vertex_transitiveb (lexprod D1 D2).
Proof.
move=> /vertex_transitivebP vt1 /vertex_transitivebP vt2.
apply/vertex_transitivebP=> u v.
have [p1 p1aut p1E] := vt1 u.1 v.1.
have [p2 p2aut p2E] := vt2 u.2 v.2.
pose pf (x : lexprod D1 D2) : lexprod D1 D2 := (p1 x.1, p2 x.2).
have pf_inj : injective pf.
  by move=> [x1 x2] [y1 y2] [/perm_inj e1 /perm_inj e2]; rewrite e1 e2.
exists (perm pf_inj).
- rewrite dgautE; apply/autbP=> x y; rewrite !permE !lexprod_arcE /=.
  move: p1aut p2aut; rewrite !dgautE => /autbP a1 /autbP a2.
  by rewrite a1 a2 (inj_eq (@perm_inj _ p1)).
- by rewrite permE /pf p1E p2E -surjective_pairing.
Qed.

End LexProdVT.
