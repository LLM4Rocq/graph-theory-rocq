(** * Digraph.conjectures.hero_isoclosure — hero iso-closure + Berger's
      "every transitive tournament is a hero" direction.

    The inductive [hero] predicate of heroes.v is built on the CONCRETE
    constructions [K1], [djoin], [c3sub]; it is therefore not literally closed
    under digraph isomorphism, and a transitive tournament [TT l] is not
    SYNTACTICALLY a domination join.  This file adds:

      - [is_hero]      : the iso-closure of [hero] ([exists H', hero H' /\ dgiso H' H]);
      - its basic theory ([hero_is_hero], [is_hero] dgiso-invariance, the
        construction closures lifted to [is_hero]);
      - the blocked Berger piece [is_hero_TT : forall l, is_hero (TT l)] — every
        transitive tournament is a hero — via the explicit isomorphism
        [dgiso (djoin K1 (TT l)) (TT l.+1)] (the source dominates the rest);
      - the resulting edge [transitive_tournament H -> dgiso H (TT #|H|)] is the
        missing bridge; carried as a hypothesis, it yields
        [transitive_tournament H -> is_hero H] (a step toward Berger's ⟸ direction).

    Everything is axiom-free (Print Assumptions: Closed under the global context).
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P6). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph Require Import dichromatic heroes heroes_dichotomy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The iso-closure of [hero] *)

(** A digraph is a HERO (closed form) when it is isomorphic to an inductively
    built [hero].  This is the predicate one actually wants: it is preserved by
    isomorphism and contains every [TT l] (proved below). *)
Definition is_hero (H : diGraphType) : Prop :=
  exists H' : diGraphType, hero H' /\ dgiso H' H.

(** Every inductive hero is a hero. *)
Lemma hero_is_hero (H : diGraphType) : hero H -> is_hero H.
Proof. by move=> hH; exists H; split=> //; apply: dgiso_refl. Qed.

(** [is_hero] is invariant under digraph isomorphism. *)
Lemma is_hero_dgiso (H1 H2 : diGraphType) :
  dgiso H1 H2 -> is_hero H1 -> is_hero H2.
Proof.
move=> iso [H' [hH' iso']]; exists H'; split=> //.
exact: dgiso_trans iso' iso.
Qed.

Lemma is_hero_dgisoW (H1 H2 : diGraphType) :
  dgiso H1 H2 -> is_hero H1 <-> is_hero H2.
Proof.
by move=> iso; split; [apply: is_hero_dgiso | apply: is_hero_dgiso (dgiso_sym iso)].
Qed.

(** ** Construction closures lifted to [is_hero] *)

Lemma is_hero_K1 : is_hero K1.
Proof. exact/hero_is_hero/hero_K1. Qed.

(** [djoin] of [is_hero]es is an [is_hero] (via [dgiso] on each block; we only
    need the special case where the blocks are inductive heroes, which is what
    the [TT] induction below uses, but state the general lift for reuse). *)
Lemma is_hero_djoin (H1 H2 : diGraphType) :
  hero H1 -> hero H2 -> is_hero (djoin H1 H2).
Proof. by move=> h1 h2; apply: hero_is_hero; apply: hero_djoin. Qed.

(** ** The Berger piece: [TT l] is a hero

    The key isomorphism: a transitive tournament on [l.+1] vertices is the
    domination join of its source [K1 = TT 1] over the transitive tournament
    [TT l] on the remaining vertices. *)

Section TT_djoin.
Variable l : nat.

(** The forward map [djoin K1 (TT l) -> TT l.+1]: the unique source [inl] goes to
    the minimum [ord0], and [inr k] goes to [k.+1 = lift ord0 k]. *)
Definition tt_join_map (x : djoin K1 (TT l)) : TT l.+1 :=
  match x with
  | inl _ => ord0
  | inr k => lift ord0 k
  end.

(** Its inverse [TT l.+1 -> djoin K1 (TT l)]: [ord0] goes to the source, and any
    other [i] goes to [inr] of its predecessor (obtained via [unlift ord0]). *)
Definition tt_join_inv (i : TT l.+1) : djoin K1 (TT l) :=
  match unlift ord0 i with
  | Some k => inr k
  | None => inl ord0
  end.

Lemma tt_join_mapK : cancel tt_join_map tt_join_inv.
Proof.
case=> [a | k]; rewrite /tt_join_map /tt_join_inv.
- by rewrite unlift_none; congr inl; case: a => -[|//] ?; apply: val_inj.
- by rewrite liftK.
Qed.

Lemma tt_join_invK : cancel tt_join_inv tt_join_map.
Proof.
by move=> i; rewrite /tt_join_inv; case: unliftP => [k -> | -> //].
Qed.

Lemma tt_join_map_bij : bijective tt_join_map.
Proof. exact: (Bijective tt_join_mapK tt_join_invK). Qed.

(** The map preserves and reflects arcs, so it is a digraph isomorphism. *)
Lemma tt_join_arc (x y : djoin K1 (TT l)) :
  (tt_join_map x --> tt_join_map y) = (x --> y).
Proof.
case: x y => [a | j] [b | k] /=; rewrite arcTTE /= ?bump0 /arc /= /djoin_rel.
- (* inl,inl : both sources; K1 = TT 1 so no arc, and ord0 </ ord0 *)
  by rewrite arcTTE; case: a => -[|//] ?; case: b => -[|//] ?.
- (* inl,inr : source dominates, 0 < k.+1 *)
  by [].
- (* inr,inl : reverse, j.+1 </ 0 *)
  by rewrite ltn0.
- (* inr,inr : TT l ordering, j.+1 < k.+1 = j < k *)
  by rewrite ltnS arcTTE.
Qed.

Lemma dgiso_djoin_TT : dgiso (djoin K1 (TT l)) (TT l.+1).
Proof. by exists tt_join_map; split; [exact: tt_join_map_bij | exact: tt_join_arc]. Qed.

End TT_djoin.

(** [TT 0] is the empty tournament; for faithfulness we record that the hero
    recursion starts at [TT 1 = K1].  Berger's heroes are nonempty, so the
    natural statement is over [l.+1] (equivalently, [TT l] for [l >= 1]). *)
Lemma is_hero_TT1 : is_hero (TT 1).
Proof. exact: is_hero_K1. Qed.

(** Every nonempty transitive tournament [TT l.+1] is a hero. *)
Lemma is_hero_TT_succ : forall l : nat, is_hero (TT l.+1).
Proof.
elim=> [|l IH]; first exact: is_hero_TT1.
(* TT l.+2 ≅ djoin K1 (TT l.+1); K1 hero, TT l.+1 is_hero by IH *)
apply: (is_hero_dgiso (dgiso_djoin_TT l.+1)).
case: IH => [H' [hH' iso']].
exists (djoin K1 H'); split; first by apply: hero_djoin => //; apply: hero_K1.
(* dgiso (djoin K1 H') (djoin K1 (TT l.+1)) from H' ≅ TT l.+1 *)
case: iso' => [f [bij_f arcf]].
exists (fun x => match x with inl a => inl a | inr b => inr (f b) end).
split.
- have [g fK gK] := bij_f.
  exists (fun x => match x with inl a => inl a | inr b => inr (g b) end).
  + by case=> [a | b] //=; rewrite fK.
  + by case=> [a | b] //=; rewrite gK.
- by case=> [a | b] [c | d] //=; rewrite /arc /= /djoin_rel ?arcf.
Qed.

(** ** Edges toward Berger's characterization

    The structural bridge: a transitive tournament on [n] vertices is isomorphic
    to [TT n].  This is the missing combinatorial fact (a transitive tournament
    is a linear order, hence order-isomorphic to [{0,..,n-1}]); we carry it as an
    explicit hypothesis rather than admitting it, keeping the edge Qed-closed. *)
Definition tt_is_TT : Prop :=
  forall H : diGraphType, transitive_tournament H -> dgiso H (TT #|H|).

(** Given that bridge, every transitive tournament is a hero — a step toward the
    ⟸ direction of Berger's dichotomy (transitive tournaments are heroes), once
    one knows transitive tournaments are nonempty. *)
Theorem tt_is_TT_implies_transitive_is_hero :
  tt_is_TT ->
  forall H : diGraphType,
    transitive_tournament H -> (0 < #|H|)%N -> is_hero H.
Proof.
move=> bridge H tH; have iso := bridge H tH.
case: #|H| iso => [//| n] iso _.
apply: (is_hero_dgiso (dgiso_sym iso)).
exact: is_hero_TT_succ.
Qed.

(** The plain ([>= 1]) restatement most directly comparable to the corpus
    target: every nonempty transitive tournament [TT n.+1] is a hero. *)
Theorem transitive_TT_is_hero : forall n : nat, is_hero (TT n.+1).
Proof. exact: is_hero_TT_succ. Qed.
