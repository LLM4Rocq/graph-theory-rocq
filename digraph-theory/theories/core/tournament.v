(** * Digraph.tournament — tournaments as an HB structure

    A tournament is a finite digraph whose arc relation is irreflexive and
    *total*: for distinct [u], [v], exactly one of [u --> v], [v --> u] holds.
    The totality axiom is stated as a boolean equation
    [(u != v) = (u --> v) (+) (v --> u)], which packs "exactly one" (xor) and
    its failure on the diagonal into a single rewritable fact.

    Contents:
    - the [Tournament] structure ([tournament]);
    - basic arc calculus (asymmetry, totality as rewriting rules);
    - in/out-neighbourhoods;
    - decidable transitivity [transb] and the 3-cycle dichotomy: a tournament
      is intransitive iff it contains a directed triangle;
    - sub-tournaments (every subtype of a tournament is one);
    - the two basic examples: the directed triangle [C3] and the transitive
      tournament [TT n]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Tournaments extend ORIENTED digraphs by totality (CK3 refactor, D9):
    [DiGraph ≤ Oriented ≤ Tournament]. The original all-in-one interface is
    kept as the [DiGraph_IsTournament] factory, so instance builders are
    unchanged and every tournament instance is an oriented digraph. *)

HB.mixin Record Oriented_IsTournament V of Oriented V := {
  arc_total : forall u v : V, (u != v) = (arc u v) (+) (arc v u)
}.

#[short(type="tournament")]
HB.structure Definition Tournament :=
  { V of Oriented V & Oriented_IsTournament V }.

HB.factory Record DiGraph_IsTournament V of DiGraph V := {
  arc_irrefl : irreflexive (arc : rel V);
  arc_total  : forall u v : V, (u != v) = (arc u v) (+) (arc v u)
}.

HB.builders Context V of DiGraph_IsTournament V.

Fact asymm (u v : V) : arc u v -> arc v u = false.
Proof.
move=> auv.
have uDv : u != v by apply: contraTneq auv => ->; rewrite arc_irrefl.
by have := arc_total u v; rewrite uDv auv /=; case: (arc v u).
Qed.

HB.instance Definition _ := DiGraph_IsOriented.Build V arc_irrefl asymm.
HB.instance Definition _ := Oriented_IsTournament.Build V arc_total.

HB.end.

(** ** Basic arc calculus *)

Section TournamentTheory.
Variable T : tournament.
Implicit Types u v w : T.

Lemma arcxx u : (u --> u) = false.
Proof. exact: arc_irrefl. Qed.

Lemma arc_neq u v : u --> v -> u != v.
Proof. by apply: contraTneq => ->; rewrite arcxx. Qed.

Lemma arc_asym u v : u --> v -> ~~ (v --> u).
Proof.
move=> uv; have := arc_total u v; rewrite (arc_neq uv) uv /=.
by case: (v --> u).
Qed.

(** On distinct vertices, the two arc directions are complementary. *)
Lemma arcNarc u v : u != v -> (u --> v) = ~~ (v --> u).
Proof.
by move=> uDv; have := arc_total u v; rewrite uDv; case: (v --> u); case: (u --> v).
Qed.

Lemma arc_or u v : u != v -> (u --> v) || (v --> u).
Proof. by move=> uDv; rewrite (arcNarc uDv) orNb. Qed.

(** Since both directions never hold together, xor and or coincide. *)
Lemma arc_xorE u v : (u --> v) (+) (v --> u) = (u --> v) || (v --> u).
Proof.
case e: (u --> v) => /=; last by [].
by rewrite (negbTE (arc_asym e)).
Qed.

(** ** Neighbourhoods *)

Definition N_out u := [set v | u --> v].
Definition N_in u := [set v | v --> u].

Lemma N_outE u v : (v \in N_out u) = (u --> v). Proof. by rewrite inE. Qed.
Lemma N_inE u v : (v \in N_in u) = (v --> u). Proof. by rewrite inE. Qed.

Lemma N_out_in_partition u :
  [set~ u] = N_out u :|: N_in u /\ [disjoint N_out u & N_in u].
Proof.
split.
- by apply/setP=> v; rewrite !inE eq_sym arc_total arc_xorE.
- rewrite disjoints_subset; apply/subsetP=> v; rewrite !inE => uv.
  exact: arc_asym.
Qed.

(** ** Decidable transitivity and the 3-cycle dichotomy *)

Definition transb := [forall u : T, [forall v : T, [forall w : T,
  (u --> v) ==> (v --> w) ==> (u --> w)]]].

Lemma transbP : reflect (transitive (arc : rel T)) transb.
Proof.
apply: (iffP idP) => [tr y x z xy yz | tr].
- by have /forallP/(_ x)/forallP/(_ y)/forallP/(_ z) := tr; rewrite xy yz.
- apply/forallP=> u; apply/forallP=> v; apply/forallP=> w.
  by apply/implyP=> uv; apply/implyP=> vw; apply: tr vw.
Qed.

(** A tournament fails transitivity exactly when it has a directed triangle. *)
Lemma ntransbP :
  reflect (exists u v w, [/\ u --> v, v --> w & w --> u]) (~~ transb).
Proof.
apply: (iffP idP) => [|[u] [v] [w] [uv vw wu]]; last first.
  apply/negP=> /transbP tr; have uw := tr _ _ _ uv vw.
  by have := arc_asym wu; rewrite uw.
rewrite negb_forall => /existsP[u]; rewrite negb_forall => /existsP[v].
rewrite negb_forall => /existsP[w]; rewrite !negb_imply => /and3P[uv vw Nuw].
have wDu : w != u.
  apply: contraNneq Nuw => wu; move: uv vw; rewrite -{1}wu => wv /arc_asym.
  by rewrite wv.
by exists u, v, w; split; rewrite // (arcNarc wDu).
Qed.

(** An intransitive tournament has at least 3 vertices. *)
Lemma ntransb_card : ~~ transb -> 3 <= #|T|.
Proof.
case/ntransbP=> u [v] [w] [uv vw wu].
have uDv := arc_neq uv; have vDw := arc_neq vw; have wDu := arc_neq wu.
have <- : #|[set u; v; w]| = 3.
  by rewrite -setUA cardsU1 !inE negb_or uDv eq_sym wDu cards2 vDw.
exact: max_card.
Qed.

Lemma card_le2_transb : #|T| <= 2 -> transb.
Proof. by apply: contraLR; rewrite -ltnNge; apply: ntransb_card. Qed.

End TournamentTheory.

(** ** Sub-tournaments: subtypes of a tournament are tournaments *)

Section SubTournament.
Variables (T : tournament) (P : pred T).

(** The subtype already carries the [Oriented] structure (core/oriented.v);
    only totality is added here. *)
Fact sub_arc_total (u v : {x : T | P x}) :
  (u != v) = (arc u v) (+) (arc v u).
Proof. by rewrite -val_eqE !sub_arcE arc_total. Qed.

HB.instance Definition _ :=
  Oriented_IsTournament.Build {x | P x} sub_arc_total.

End SubTournament.

(** Object-level versions for use in statements. *)

Definition sub_tournament (T : tournament) (S : {set T}) : tournament :=
  {x : T | x \in S} : tournament.

Definition del_tournament (T : tournament) (v : T) : tournament :=
  sub_tournament [set~ v].

(** ** Example 1: the directed triangle [C3] *)

Section C3.
Local Open Scope ring_scope.
Import GRing.Theory.

Definition C3 : Type := 'Z_3.

HB.instance Definition _ := Finite.on C3.
HB.instance Definition _ := HasArc.Build C3 [rel u v : 'Z_3 | v == u + 1].

Fact C3_irrefl : irreflexive (arc : rel C3).
Proof. by case=> -[|[|[|//]]] ?. Qed.

Fact C3_total (u v : C3) : (u != v) = (arc u v) (+) (arc v u).
Proof. by case: u v => -[|[|[|//]]] ? [[|[|[|//]]] ?]. Qed.

HB.instance Definition _ := DiGraph_IsTournament.Build C3 C3_irrefl C3_total.

Lemma arcC3E (u v : C3) : (u --> v) = (v == u + 1 :> 'Z_3).
Proof. by []. Qed.

Lemma card_C3 : #|{: C3}| = 3.
Proof. by rewrite card_ord. Qed.

(** C3 is the directed triangle: it is *not* transitive. *)
Lemma C3_Ntransb : ~~ transb (C3 : tournament).
Proof.
by apply/ntransbP; exists 0, 1, (1 + 1); split; rewrite arcC3E ?add0r.
Qed.

End C3.

(** ** Example 2: transitive tournaments [TT n] *)

Section TT.
Variable n : nat.

Definition TT : Type := 'I_n.

HB.instance Definition _ := Finite.on TT.
HB.instance Definition _ := HasArc.Build TT [rel u v : 'I_n | u < v].

Fact TT_irrefl : irreflexive (arc : rel TT).
Proof. by move=> u; exact: ltnn. Qed.

Fact TT_total (u v : TT) : (u != v) = (arc u v) (+) (arc v u).
Proof.
have h (a b : 'I_n) : (a != b) = ((a < b) (+) (b < a))%N.
  by rewrite -val_eqE neq_ltn; case: ltngtP.
exact: h.
Qed.

HB.instance Definition _ := DiGraph_IsTournament.Build TT TT_irrefl TT_total.

Lemma arcTTE (u v : TT) : (u --> v) = (u < v)%N.
Proof. by []. Qed.

Lemma card_TT : #|{: TT}| = n.
Proof. by rewrite card_ord. Qed.

Lemma TT_transb : transb (TT : tournament).
Proof. by apply/transbP=> y x z; rewrite !arcTTE; apply: ltn_trans. Qed.

End TT.
