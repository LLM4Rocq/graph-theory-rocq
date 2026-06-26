(** * Digraph.conjectures.grounding_heroes — GROUNDING heroes.v

    Faithfulness checks for [heroes.v] (Forb_ind / hero, Berger et al.,
    Aboulker–Charbit–Naserasr arXiv:2009.13319, Berger et al. JCTB 2015).

    Each lemma ties a NEW definition to a KNOWN textbook fact:

      - [ind_subdigraph] is a preorder (reflexive + transitive) — the
        induced-subdigraph relation is a containment order (textbook);
      - [hero K1] : the single vertex is the base hero (Berger recursion base);
      - the DIRECTED TRIANGLE [c3sub K1 (TT 1) K1] is a hero, and is
        digraph-isomorphic to [C3] — C₃ is the simplest non-transitive hero
        (Berger Thm 2.2; the directed triangle bounds the dichromatic number);
      - [is_tournament] holds for [C3] and every [TT n] (definitional sanity:
        the committed tournament instances satisfy the spelled-out predicate);
      - every transitive tournament [TT n.+1] is a hero (re-derived here from the
        Berger recursion, via [TT n.+1 ≅ djoin K1 (TT n)]) — transitive
        tournaments are heroes (Berger).

    RED-FLAG probe: [hero] must NOT collapse to "every digraph". We exhibit a
    2-vertex digraph (the EDGELESS pair / the DIGON) that is provably NOT a
    tournament, hence by Berger NOT a hero — a sanity ceiling on the predicate.

    Imports ONLY committed modules + [heroes.v] (the file under grounding). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dichromatic.
From Digraph Require Import heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [ind_subdigraph] is a preorder

    Grounds: the induced-subdigraph relation is reflexive and transitive
    (a containment order on digraphs — standard). *)

Lemma ind_subdigraph_refl (D : diGraphType) : ind_subdigraph D D.
Proof. by exists id; split=> // x y. Qed.

Lemma ind_subdigraph_trans (D1 D2 D3 : diGraphType) :
  ind_subdigraph D1 D2 -> ind_subdigraph D2 D3 -> ind_subdigraph D1 D3.
Proof.
case=> f [injf arcf] [g [injg arcg]]; exists (g \o f); split.
  by apply: inj_comp.
by move=> u v /=; rewrite arcg arcf.
Qed.

(** ** Berger recursion base: K1 is a hero *)

Lemma grounding_hero_K1 : hero K1.
Proof. exact: hero_K1. Qed.

(** ** The directed triangle is a hero

    [c3sub K1 (TT 1) K1] is the substitution of three singletons into C₃; it is
    exactly the directed triangle and is a hero by one [hero_c3L] step (k = 1,
    inner hero [K1]). This is the simplest NON-transitive Berger hero. *)

Definition dtri : diGraphType := c3sub K1 (TT 1) K1.

Lemma grounding_hero_dtri : hero dtri.
Proof. exact: (hero_c3L 1 hero_K1). Qed.

(** [dtri] really is the directed triangle: it is isomorphic to [C3].
    The bijection sends the three singleton blocks to 0,1,2 ∈ ℤ/3 in cyclic
    order; both relations are "next vertex around the triangle". *)

Section DtriIsC3.

(* [C3 = 'Z_3] reduces to ['I_3]; we name its three vertices as ordinals. *)
Definition z3_0 : C3 := @Ordinal 3 0 isT.
Definition z3_1 : C3 := @Ordinal 3 1 isT.
Definition z3_2 : C3 := @Ordinal 3 2 isT.

(* The vertex type of [dtri] is ((K1 + TT 1) + K1) = (('I_1 + 'I_1) + 'I_1). *)
Definition dtri_to_C3 (x : dtri) : C3 :=
  match x with
  | inl (inl _) => z3_0
  | inl (inr _) => z3_1
  | inr _       => z3_2
  end.

Definition C3_to_dtri (z : C3) : dtri :=
  match val z with
  | 0    => inl (inl ord0)
  | 1    => inl (inr ord0)
  | _    => inr ord0
  end.

Lemma ord1_eq0 (a : 'I_1) : a = ord0.
Proof. by apply/val_inj; case: a => -[|//]. Qed.

Lemma dtri_C3_can : cancel dtri_to_C3 C3_to_dtri.
Proof.
case=> [[a | b] | c] /=.
- by rewrite (ord1_eq0 a).
- by rewrite (ord1_eq0 b).
- by rewrite (ord1_eq0 c).
Qed.

Lemma C3_dtri_can : cancel C3_to_dtri dtri_to_C3.
Proof. by case=> -[|[|[|//]]] ?; apply/val_inj. Qed.

Lemma dtri_to_C3_bij : bijective dtri_to_C3.
Proof. by exists C3_to_dtri; [exact: dtri_C3_can | exact: C3_dtri_can]. Qed.

Lemma dtri_to_C3_arc (u v : dtri) :
  (dtri_to_C3 u --> dtri_to_C3 v) = (u --> v).
Proof.
by case: u v => [[[[|//] ?]|[[|//] ?]]|[[|//] ?]] [[[[|//] ?]|[[|//] ?]]|[[|//] ?]].
Qed.

Lemma dgiso_dtri_C3 : dgiso dtri C3.
Proof. by exists dtri_to_C3; split; [exact: dtri_to_C3_bij | exact: dtri_to_C3_arc]. Qed.

End DtriIsC3.

(** ** [is_tournament] holds for the committed tournament instances

    Grounds: the spelled-out [is_tournament] predicate (irreflexive +
    semicomplete + asymmetric) is satisfied by [C3] and every [TT n]
    (which carry the [tournament] HB instance). A definitional sanity check:
    [is_tournament] must agree with the structure on the canonical examples. *)

Lemma is_tournament_of (T : tournament) : is_tournament T.
Proof.
split.
- exact: arc_irrefl.
- by move=> u v; exact: arc_or.
- by move=> u v; exact: arc_asym.
Qed.

Lemma is_tournament_C3 : is_tournament C3.
Proof. exact: (is_tournament_of C3). Qed.

Lemma is_tournament_TT (n : nat) : is_tournament (TT n).
Proof. exact: (is_tournament_of (TT n)). Qed.

(** ** Transitive tournaments are heroes (re-derived)

    Grounds: every transitive tournament is a hero (Berger). The inductive
    [hero] is NOT literally closed under [dgiso] (its constructors only ever
    yield [djoin]/[c3sub] vertex types, never the literal type [TT n.+1]); the
    faithful notion is therefore the ISO-CLOSURE [is_hero] (matching the design
    of the corpus's [hero_isoclosure.v]). We re-derive it locally and prove
    every nonempty transitive tournament [TT n.+1] satisfies it, via the key
    isomorphism [TT n.+1 ≅ djoin K1 (TT n)]. *)

Definition is_hero (H : diGraphType) : Prop :=
  exists H', hero H' /\ dgiso H' H.

Lemma hero_is_hero (H : diGraphType) : hero H -> is_hero H.
Proof. by move=> hH; exists H; split=> //; apply: dgiso_refl. Qed.

Lemma is_hero_dgiso (H1 H2 : diGraphType) :
  dgiso H1 H2 -> is_hero H1 -> is_hero H2.
Proof.
by move=> iso [H' [hH' iso']]; exists H'; split=> //; exact: dgiso_trans iso' iso.
Qed.

Lemma is_hero_K1 : is_hero K1.
Proof. exact/hero_is_hero/hero_K1. Qed.

(* The directed triangle [C3] is an [is_hero] (iso-closure of the hero [dtri]). *)
Lemma is_hero_C3 : is_hero C3.
Proof. by exists dtri; split; [exact: grounding_hero_dtri | exact: dgiso_dtri_C3]. Qed.

(** Key iso [TT l.+1 ≅ djoin K1 (TT l)], re-derived. *)
Section TT_djoin.
Variable l : nat.

Definition tt_join_map (x : djoin K1 (TT l)) : TT l.+1 :=
  match x with inl _ => ord0 | inr k => lift ord0 k end.

Definition tt_join_inv (i : TT l.+1) : djoin K1 (TT l) :=
  match unlift ord0 i with Some k => inr k | None => inl ord0 end.

Lemma tt_join_mapK : cancel tt_join_map tt_join_inv.
Proof.
case=> [a | k]; rewrite /tt_join_map /tt_join_inv.
- by rewrite unlift_none; congr inl; case: a => -[|//] ?; apply: val_inj.
- by rewrite liftK.
Qed.

Lemma tt_join_invK : cancel tt_join_inv tt_join_map.
Proof. by move=> i; rewrite /tt_join_inv; case: unliftP => [k -> | -> //]. Qed.

Lemma tt_join_map_bij : bijective tt_join_map.
Proof. exact: (Bijective tt_join_mapK tt_join_invK). Qed.

Lemma tt_join_arc (x y : djoin K1 (TT l)) :
  (tt_join_map x --> tt_join_map y) = (x --> y).
Proof.
case: x y => [a | j] [b | k] /=; rewrite arcTTE /= ?bump0 /arc /= /djoin_rel.
- by rewrite arcTTE; case: a => -[|//] ?; case: b => -[|//] ?.
- by [].
- by rewrite ltn0.
- by rewrite ltnS arcTTE.
Qed.

Lemma dgiso_djoin_TT : dgiso (djoin K1 (TT l)) (TT l.+1).
Proof. by exists tt_join_map; split; [exact: tt_join_map_bij | exact: tt_join_arc]. Qed.

End TT_djoin.

(** Every nonempty transitive tournament [TT l.+1] is an [is_hero]. *)
Lemma is_hero_TT_succ : forall l : nat, is_hero (TT l.+1).
Proof.
elim=> [|l IH]; first exact: is_hero_K1.
apply: (is_hero_dgiso (dgiso_djoin_TT l.+1)).
case: IH => [H' [hH' iso']].
exists (djoin K1 H'); split; first by apply: hero_djoin => //; apply: hero_K1.
case: iso' => [f [bij_f arcf]].
exists (fun x => match x with inl a => inl a | inr b => inr (f b) end).
split.
- have [g fK gK] := bij_f.
  exists (fun x => match x with inl a => inl a | inr b => inr (g b) end).
  + by case=> [a | b] //=; rewrite fK.
  + by case=> [a | b] //=; rewrite gK.
- by case=> [a | b] [c | d] //=; rewrite /arc /= /djoin_rel ?arcf.
Qed.

Theorem grounding_transitive_TT_is_hero : forall n : nat, is_hero (TT n.+1).
Proof. exact: is_hero_TT_succ. Qed.

(** ** RED-FLAG probe: [hero] is NOT trivially everything

    Berger heroes are tournaments. We exhibit two 2-vertex digraphs that are
    provably NOT tournaments, hence cannot be heroes (a hero is a tournament):

      - [Edgeless2] : two vertices, no arcs — fails SEMICOMPLETENESS;
      - [Digon2]    : two vertices with arcs both ways — fails ASYMMETRY.

    We prove [~ is_tournament _] for both, the sanity ceiling on the hero
    predicate (if these were heroes, [hero] would be vacuous). *)

(* Edgeless 2-vertex digraph. *)
Definition er2 (_ _ : 'I_2) : bool := false.
Definition Edgeless2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on Edgeless2_car.
HB.instance Definition _ := HasArc.Build Edgeless2_car er2.
Definition Edgeless2 : diGraphType := Edgeless2_car.

Lemma Edgeless2_not_tournament : ~ is_tournament Edgeless2.
Proof.
case=> _ semi _.
have d01 : (ord0 : Edgeless2) != (Ordinal (isT : 1 < 2)) by [].
by have := semi _ _ d01; rewrite /arc /= /er2.
Qed.

(* Digon: two vertices with arcs both ways. *)
Definition dr2 (x y : 'I_2) : bool := x != y.
Definition Digon2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on Digon2_car.
HB.instance Definition _ := HasArc.Build Digon2_car dr2.
Definition Digon2 : diGraphType := Digon2_car.

Lemma Digon2_not_tournament : ~ is_tournament Digon2.
Proof.
case=> _ _ asym.
have a01 : (ord0 : Digon2) --> (Ordinal (isT : 1 < 2)) by [].
have a10 : (Ordinal (isT : 1 < 2) : Digon2) --> (ord0 : Digon2) by [].
by have := asym _ _ a01; rewrite a10.
Qed.
