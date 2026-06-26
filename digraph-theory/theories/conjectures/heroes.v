(** * Digraph.conjectures.heroes — P6: Forb_ind + the hero predicate

    The Gyárfás–Sumner / heroes corpus (Aboulker–Charbit–Naserasr, arXiv:2009.13319 and
    Berger et al., JCTB 2015). This file builds the two pieces the cluster needs on top of
    the dichromatic keystone (P2):

      - induced-subdigraph containment and the [Forb_ind] / [heroic] vocabulary;
      - the [hero] predicate via Berger's recursion (K₁, domination join, C₃-substitution),
        for which we add the two digraph constructions [djoin] (H₁ ⇒ H₂) and [c3sub]
        (C₃(D₁,D₂,D₃), substitution into the directed triangle).

    Statements here: the umbrella [heroic] predicate (Problem 1.2 asks to characterize the
    heroic forbidden sets), and Berger's characterization [berger_characterization]
    (a hero is exactly a tournament whose forbidding bounds the dichromatic number).
    The hero-dichotomy conjectures (4.2/4.4) and the small-pattern values (6.2 / Thm 6.1)
    build on these and follow in a subsequent P6 step.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P6), §2. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Induced-subdigraph containment and forbidden classes *)

(** [H] embeds as an INDUCED subdigraph of [D]: an injection preserving and reflecting
    arcs (so the image induces a copy of [H]). *)
Definition ind_subdigraph (H D : diGraphType) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, (f u --> f v) = (u --> v).

Definition ind_free (H D : diGraphType) : Prop := ~ ind_subdigraph H D.

(** The class [Forb_ind forb] of digraphs avoiding every member of the forbidden
    family [forb] as an induced subdigraph. (A predicate-valued family handles both finite
    sets and the "all orientations of an undirected graph" extension uniformly.) *)
Definition Forb_ind (forb : diGraphType -> Prop) (D : diGraphType) : Prop :=
  forall H : diGraphType, forb H -> ind_free H D.

(** A forbidden family is HEROIC when its class has bounded dichromatic number. *)
Definition heroic (forb : diGraphType -> Prop) : Prop :=
  dichromatic_bounded (Forb_ind forb).

(** ** Hero-building digraph constructions *)

(** Domination join [H₁ ⇒ H₂]: disjoint union with every arc directed from [H₁] to [H₂]. *)
Section DJoin.
Variables D1 D2 : diGraphType.
Definition djoin : Type := (D1 + D2)%type.
HB.instance Definition _ := Finite.on djoin.
Definition djoin_rel (x y : D1 + D2) : bool :=
  match x, y with
  | inl a, inl b => arc a b
  | inr a, inr b => arc a b
  | inl _, inr _ => true
  | inr _, inl _ => false
  end.
HB.instance Definition _ := HasArc.Build djoin djoin_rel.
End DJoin.

(** C₃-substitution [C₃(D₁,D₂,D₃)]: substitute the three blocks into the directed
    triangle, with every arc directed cyclically D₁ ⇒ D₂ ⇒ D₃ ⇒ D₁ between blocks. *)
Section C3sub.
Variables D1 D2 D3 : diGraphType.
Definition c3sub : Type := (D1 + D2 + D3)%type.
HB.instance Definition _ := Finite.on c3sub.
Definition c3sub_rel (x y : D1 + D2 + D3) : bool :=
  match x, y with
  | inl (inl a), inl (inl a') => arc a a'
  | inl (inr b), inl (inr b') => arc b b'
  | inr c, inr c' => arc c c'
  | inl (inl _), inl (inr _) => true
  | inl (inr _), inr _ => true
  | inr _, inl (inl _) => true
  | _, _ => false
  end.
HB.instance Definition _ := HasArc.Build c3sub c3sub_rel.
End C3sub.

(** ** The hero predicate (Berger et al., Theorem 2.2)

    [K₁] is the single-vertex tournament. A tournament is a HERO when it is built from
    [K₁] by domination joins and by substituting a hero and a transitive tournament into
    two of the three positions of the directed triangle. *)
Definition K1 : diGraphType := TT 1.

Inductive hero : diGraphType -> Prop :=
| hero_K1    : hero K1
| hero_djoin : forall H1 H2 : diGraphType, hero H1 -> hero H2 -> hero (djoin H1 H2)
| hero_c3L   : forall (H : diGraphType) (k : nat), hero H -> hero (c3sub H (TT k) K1)
| hero_c3R   : forall (H : diGraphType) (k : nat), hero H -> hero (c3sub (TT k) H K1).

(** ** Problem 1.2 and Berger's characterization *)

(** Problem 1.2 (the umbrella): characterize the finite forbidden families that are
    [heroic]. As an open-ended classification it has no single-[Prop] form; the
    formalizable nucleus is the [heroic] predicate above. *)

(** A digraph is a tournament: irreflexive, semicomplete (any two distinct vertices
    adjacent), and asymmetric (no digon). Equivalently the class
    [Forb_ind({digon, K̄₂})]. *)
Definition is_tournament (D : diGraphType) : Prop :=
  [/\ irreflexive (@arc D),
      (forall u v : D, u != v -> (u --> v) || (v --> u))
    & (forall u v : D, u --> v -> ~~ (v --> u))].

(** Berger's characterization (Theorem 2.2, a proved external result stated as a target):
    a tournament [H] is a hero iff forbidding it (within tournaments) keeps the dichromatic
    number bounded — i.e. iff the set {digon, K̄₂, H} is heroic. *)
Definition berger_characterization : Prop :=
  forall H : diGraphType,
    hero H <-> dichromatic_bounded (fun D => is_tournament D /\ ind_free H D).
