(** arXiv:1812.02420, Problem 5.40: no directed Kneser graph for (5,3).
    This refutes X2.directed_kneser_existence_statement. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented dipath tournament dichromatic X2.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma acyclic_from_rank (D : diGraphType) (rank : D -> nat) :
  (forall x y : D, x --> y -> rank x < rank y) -> acyclicb D.
Proof.
move=> inc; apply/forallP=> v; apply/forallP=> w; apply/implyP=> vw.
apply/negP=> /connectP[s ps lastE].
have le : rank w <= rank v.
  rewrite lastE; elim: s w ps {vw lastE} => [|y s IH] w /=; first by rewrite leqnn.
  case/andP=> wy ys; exact: leq_trans (ltnW (inc _ _ wy)) (IH y ys).
by move: le; rewrite leqNgt (inc _ _ vw).
Qed.

Lemma acyclic_from_transitive (D : diGraphType) :
  irreflexive (arc : rel D) -> transitive (arc : rel D) -> acyclicb D.
Proof.
move=> irr tr; apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
apply/negP=> /connectP[s ps lastE].
have arc_last : x --> last y s.
  elim: s y xy ps {lastE} => [|z s IH] y xy //= /andP[yz zs].
  exact: IH (tr _ _ _ xy yz) zs.
by move: arc_last; rewrite -lastE irr.
Qed.

Section InducedAcyclic.
Variable D : diGraphType.
Lemma induced_no_loop (X : {set D}) x :
  acyclicb (induced_digraph X) -> x \in X -> ~~ (x --> x).
Proof.
move=> ac xX; pose a : induced_digraph X := Sub x xX.
apply/negP=> xx; have bad : ~~ acyclicb (induced_digraph X).
  apply: (loop_not_acyclicb (v := a)); exact: xx.
by rewrite ac in bad.
Qed.

Lemma induced_no_digon (X : {set D}) x y :
  acyclicb (induced_digraph X) -> x \in X -> y \in X ->
  x --> y -> ~~ (y --> x).
Proof.
move=> /forallP ac xX yX xy.
pose a : induced_digraph X := Sub x xX.
pose b : induced_digraph X := Sub y yX.
have nret := implyP (forallP (ac a) b) xy.
apply/negP=> yx; have ret : connect arc b a by apply: connect1; exact: yx.
by rewrite ret in nret.
Qed.

Lemma induced_no_triangle (X : {set D}) x y z :
  acyclicb (induced_digraph X) -> x \in X -> y \in X -> z \in X ->
  x --> y -> y --> z -> ~~ (z --> x).
Proof.
move=> /forallP ac xX yX zX xy yz.
pose a : induced_digraph X := Sub x xX.
pose b : induced_digraph X := Sub y yX.
pose c : induced_digraph X := Sub z zX.
have nret := implyP (forallP (ac a) b) xy.
apply/negP=> zx; have ret : connect arc b a.
  have bc : b --> c := yz.
  have ca : c --> a := zx.
  exact: connect_trans (connect1 bc) (connect1 ca).
by rewrite ret in nret.
Qed.
End InducedAcyclic.

(** An oriented graph on three named vertices with one missing pair is acyclic. *)
Lemma three_arcless_acyclic (D : diGraphType) (a b c : D) :
  irreflexive (arc : rel D) ->
  (forall x y : D, x --> y -> ~~ (y --> x)) ->
  ~~ (a --> b) -> ~~ (b --> a) ->
  acyclicb (induced_digraph [set a; b; c]).
Proof.
move=> irr asym ab ba.
pose rho x := if x == c then 1 else if x --> c then 0 else 2.
have inc x y : x \in [set a; b; c] -> y \in [set a; b; c] ->
    x --> y -> rho x < rho y.
  move=> xX yX xy.
  case: (boolP (x == c)) => [/eqP xc | xNc].
  - subst x; case: (boolP (y == c)) => [/eqP yc | yNc].
    + by subst y; rewrite irr in xy.
    + by rewrite /rho eqxx (negbTE yNc) (negbTE (asym _ _ xy)).
  - case: (boolP (y == c)) => [/eqP yc | yNc].
    + subst y; by rewrite /rho (negbTE xNc) xy eqxx.
    + have xAB : (x == a) || (x == b).
        by move: xX; rewrite !inE (negbTE xNc) orbF.
      have yAB : (y == a) || (y == b).
        by move: yX; rewrite !inE (negbTE yNc) orbF.
      exfalso; move: xy.
      case/orP: xAB=> /eqP->; case/orP: yAB=> /eqP->;
        by rewrite ?irr ?(negbTE ab) ?(negbTE ba).

apply: (acyclic_from_rank (rank := fun x : induced_digraph [set a; b; c] => rho (val x))).
move=> x y; rewrite sub_arcE; exact: inc (valP x) (valP y).
Qed.

Section Kneser53.
Variable R : rel (bsubset 5 3).
Hypothesis KP : directed_kneser_property R.
Let D := @X2_kneser_digraph__canonical__digraph_DiGraph 5 3 R.

Lemma triple_card (B : D) : #|val B| = 3.
Proof. exact: (eqP (valP B)). Qed.

Lemma triple_nonempty (B : D) : exists i : 'I_5, i \in val B.
Proof.
have /card_gt0P[i iB] : 0 < #|val B| by rewrite triple_card.
by exists i.
Qed.

Lemma two_triples_intersect (A B : D) : exists i : 'I_5, i \in val A /\ i \in val B.
Proof.
case: (set_0Vmem (val A :&: val B))=> [emptyI | [i /setIP[iA iB]]]; last by exists i.
have union6 : #|val A :|: val B| = 6.
  have := cardsUI (val A) (val B).
  by rewrite !triple_card emptyI cards0 addn0.
have := max_card (val A :|: val B).
by rewrite union6 card_ord.
Qed.

Lemma kneser53_loopless : irreflexive (arc : rel D).
Proof.
move=> B; have [i iB] := triple_nonempty B.
have ci : common_intersection_nonempty [set B].
  exists i; move=> C /set1P->; exact: iB.
have ac := (proj2 (KP [set B])) ci.
apply/negbTE; exact: induced_no_loop ac (set11 B).
Qed.

Lemma kneser53_asymmetric (A B : D) : A --> B -> ~~ (B --> A).
Proof.
move=> AB; have [i [iA iB]] := two_triples_intersect A B.
have ci : common_intersection_nonempty [set A; B].
  exists i; move=> C /set2P[-> | ->]; assumption.
have ac := (proj2 (KP [set A; B])) ci.
apply: (induced_no_digon ac _ _ AB); by rewrite !inE eqxx ?orbT.
Qed.

Notation o0 := (@Ordinal 5 0 (erefl true)).
Notation o1 := (@Ordinal 5 1 (erefl true)).
Notation o2 := (@Ordinal 5 2 (erefl true)).
Notation o3 := (@Ordinal 5 3 (erefl true)).
Notation o4 := (@Ordinal 5 4 (erefl true)).

Definition B234 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o2 |: (o3 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B134 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o1 |: (o3 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B124 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o1 |: (o2 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B123 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o1 |: (o2 |: [set o3]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B012 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o1 |: [set o2]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B013 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o1 |: [set o3]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B014 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o1 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B023 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o2 |: [set o3]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B024 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o2 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).
Definition B034 : D := @exist {set 'I_5} (fun S => is_true (#|S| == 3)) (o0 |: (o3 |: [set o4]))
  ltac:(rewrite /= !cardsU1 cards1 !inE; by vm_compute).

Definition star_list : seq D := [:: B234; B134; B124; B123].
Definition star : {set D} := [set B | B \in star_list].

Lemma star_cases B : B \in star -> [\/ B = B234, B = B134, B = B124 | B = B123].
Proof.
rewrite inE /star_list !inE.
by move/or4P=> [/eqP->|/eqP->|/eqP->|/eqP->]; [apply: Or41|apply: Or42|apply: Or43|apply: Or44].
Qed.

Lemma star234 : B234 \in star. Proof. by rewrite inE /star_list !inE eqxx. Qed.
Lemma star134 : B134 \in star. Proof. by rewrite inE /star_list !inE eqxx orbT. Qed.
Lemma star124 : B124 \in star. Proof. by rewrite inE /star_list !inE eqxx !orbT. Qed.
Lemma star123 : B123 \in star. Proof. by rewrite inE /star_list !inE eqxx !orbT. Qed.

Lemma star_empty_intersection : ~ common_intersection_nonempty star.
Proof.
move=> [i ci].
have h234 := ci B234 star234; have h134 := ci B134 star134.
have h124 := ci B124 star124; have h123 := ci B123 star123.
clear ci; move: h234 h134 h124 h123.
case: i => -[|[|[|[|[|//]]]]] ?;
  by rewrite /B234 /B134 /B124 /B123 /= !inE.
Qed.

Lemma common_three_from (i : 'I_5) (A B C : D) :
  i \in val A -> i \in val B -> i \in val C ->
  common_intersection_nonempty [set A; B; C].
Proof.
move=> iA iB iC; exists i; move=> E.
rewrite !inE -orbA; by move/or3P=> [/eqP->|/eqP->|/eqP->].
Qed.

Lemma three_star_intersect (A B C : D) :
  A \in star -> B \in star -> C \in star ->
  common_intersection_nonempty [set A; B; C].
Proof.
move=> /star_cases ca /star_cases cb /star_cases cc.
case: ca=> ->; case: cb=> ->; case: cc=> ->;
first [ by apply: (common_three_from (i := o1)); rewrite /B234 /B134 /B124 /B123 /= !inE
      | by apply: (common_three_from (i := o2)); rewrite /B234 /B134 /B124 /B123 /= !inE
      | by apply: (common_three_from (i := o3)); rewrite /B234 /B134 /B124 /B123 /= !inE
      | by apply: (common_three_from (i := o4)); rewrite /B234 /B134 /B124 /B123 /= !inE ].
Qed.

Lemma empty_three_from (A B C : D) :
  (forall i : 'I_5, ~~ [&& i \in val A, i \in val B & i \in val C]) ->
  ~ common_intersection_nonempty [set A; B; C].
Proof.
move=> no [i ci].
have iA : i \in val A by apply: ci; rewrite !inE eqxx.
have iB : i \in val B by apply: ci; rewrite !inE eqxx orbT.
have iC : i \in val C by apply: ci; rewrite !inE eqxx orbT.
by have := no i; rewrite iA iB iC.
Qed.

Lemma two_star_empty_extension (A B : D) :
  A \in star -> B \in star -> A != B ->
  exists C : D, ~ common_intersection_nonempty [set A; B; C].
Proof.
move=> /star_cases ca /star_cases cb.
case: ca=> ->; case: cb=> ->; try by rewrite eqxx.
all: move=> _;
first [ by exists B012; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B012 /= !inE
      | by exists B013; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B013 /= !inE
      | by exists B014; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B014 /= !inE
      | by exists B023; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B023 /= !inE
      | by exists B024; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B024 /= !inE
      | by exists B034; apply: empty_three_from; case=> -[|[|[|[|[|//]]]]] ?;
           rewrite /B234 /B134 /B124 /B123 /B034 /= !inE ].
Qed.

Lemma star_arc_total (A B : D) :
  A \in star -> B \in star -> A != B -> (A --> B) || (B --> A).
Proof.
move=> AS BS AB; have [C emptyC] := two_star_empty_extension AS BS AB.
case eAB: (A --> B)=> //=; case eBA: (B --> A)=> //; exfalso.
have nAB : ~~ (A --> B) by rewrite eAB.
have nBA : ~~ (B --> A) by rewrite eBA.
have ac := three_arcless_acyclic C kneser53_loopless kneser53_asymmetric nAB nBA.
exact: emptyC ((proj1 (KP [set A; B; C])) ac).
Qed.

Lemma star_transitive : transitive (arc : rel (induced_digraph star)).
Proof.
move=> y x z xy yz.
case eXZ: (x --> z)=> //; exfalso.
have xDz : val x != val z.
  apply/negP=> /eqP xz.
  have yNx : ~~ (val y --> val x) := kneser53_asymmetric xy.
  move: yNx; rewrite xz; by rewrite -[val y --> val z]/(y --> z) yz.
have zx : val z --> val x.
  have := star_arc_total (valP x) (valP z) xDz.
  by rewrite -[val x --> val z]/(x --> z) eXZ.
have ci := three_star_intersect (valP x) (valP y) (valP z).
have ac := (proj2 (KP [set val x; val y; val z])) ci.
have hx : val x \in [set val x; val y; val z] by rewrite !inE eqxx.
have hy : val y \in [set val x; val y; val z] by rewrite !inE eqxx orbT.
have hz : val z \in [set val x; val y; val z] by rewrite !inE eqxx orbT.
have no := induced_no_triangle ac hx hy hz xy yz.
exact: (negP no zx).
Qed.

Theorem directed_kneser_53_impossible : False.
Proof.
have irr : irreflexive (arc : rel (induced_digraph star)).
  move=> x; exact: kneser53_loopless.
have ac := acyclic_from_transitive irr star_transitive.
exact: star_empty_intersection ((proj1 (KP star)) ac).
Qed.
End Kneser53.

Theorem directed_kneser_existence_disproved : ~ directed_kneser_existence_statement.
Proof.
move=> ex; have [R prop] := ex 5 3 erefl erefl.
exact: directed_kneser_53_impossible prop.
Qed.
Print Assumptions directed_kneser_existence_disproved.
