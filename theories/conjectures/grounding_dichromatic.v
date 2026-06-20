(** * Digraph.conjectures.grounding_dichromatic — faithfulness grounding for
    [dichromatic.v] (the dichromatic number χ⃗, Neumann-Lara).

    These are KNOWN, textbook-true facts that the new definitions [acyclicb],
    [dicolorableb], [dichromatic_bounded] MUST satisfy if they faithfully encode
    Neumann-Lara's dichromatic number. Each lemma is tied to the literature fact
    it grounds:

      - empty digraph is acyclic                                  (vacuously)
      - a loop kills dicolourability at every k                   (loops are
        length-1 dicycles, never acyclic)
      - dgiso-invariance of [acyclicb]                            (isomorphism
        preserves acyclicity)
      - [dicolorableb D 1 = acyclicb D]                           (χ⃗(D) ≤ 1 iff
        D is acyclic — the base of the Neumann-Lara hierarchy)
      - [dicolorableb (TT n) 1] i.e. χ⃗(TTₙ) = 1                   (a transitive
        tournament is acyclic — textbook)
      - [~~ dicolorableb C3 1] but [dicolorableb C3 2], i.e. χ⃗(C₃)=2
        (the directed triangle is the smallest non-trivial Neumann-Lara value)
      - monotonicity [dicolorableb D k -> dicolorableb D k.+1]    (more colours
        never hurt)

    RED-FLAG probe: [dicolorableb C3 1] must NOT be provable; we prove its
    negation [~~ dicolorableb C3 1] (so χ⃗(C₃) > 1, as required). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph dipath tournament.
From Digraph Require Import dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

(** ** acyclicb is dgiso-invariant

    An isomorphism of digraphs preserves acyclicity. This is the faithfulness
    bridge that lets us read [acyclicb (induced_digraph setT)] as [acyclicb D]. *)

(** connect transports along a digraph isomorphism. *)
Lemma connect_dgiso (D1 D2 : diGraphType) (f : D1 -> D2) :
  bijective f -> (forall u v, (f u --> f v) = (u --> v)) ->
  forall u v, connect arc (f u) (f v) = connect arc u v.
Proof.
move=> [g fK gK] arcE u v.
have arcE2 : forall a b : D2, (g a --> g b) = (a --> b).
  by move=> a b; rewrite -{2}[a]gK -{2}[b]gK arcE.
have pathg : forall (x : D2) s, path arc x s -> path arc (g x) (map g s).
  move=> x s; elim: s x => [|h t IH] x //=.
  by case/andP=> xh pht; rewrite arcE2 xh /= IH.
have pathf : forall (x : D1) s, path arc x s -> path arc (f x) (map f s).
  move=> x s; elim: s x => [|h t IH] x //=.
  by case/andP=> xh pht; rewrite arcE xh /= IH.
apply/idP/idP.
- move=> /connectP[s ps lastE].
  apply/connectP; exists (map g s); first by rewrite -[u]fK pathg.
  by rewrite -[u in last u _]fK last_map -lastE fK.
- move=> /connectP[s ps lastE].
  apply/connectP; exists (map f s); first by rewrite pathf.
  by rewrite last_map lastE.
Qed.

Lemma acyclicb_dgiso (D1 D2 : diGraphType) :
  dgiso D1 D2 -> acyclicb D1 = acyclicb D2.
Proof.
case=> f [bijf arcE].
have CE := connect_dgiso bijf arcE.
have [g fK gK] := bijf.
have arcE2 : forall a b : D2, (a --> b) = (g a --> g b).
  by move=> a b; rewrite -{1}[a]gK -{1}[b]gK arcE.
have CE2 : forall a b : D2, connect arc a b = connect arc (g a) (g b).
  by move=> a b; rewrite -{1}[a]gK -{1}[b]gK CE.
apply/idP/idP.
- move=> /forallP ac1; apply/forallP=> a; apply/forallP=> b; apply/implyP=> ab.
  have := implyP (forallP (ac1 (g a)) (g b)); rewrite -arcE2 ab => /(_ isT).
  by rewrite -CE2.
- move=> /forallP ac2; apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
  have := implyP (forallP (ac2 (f u)) (f v)); rewrite arcE uv => /(_ isT).
  by rewrite CE.
Qed.

(** ** Empty digraph is acyclic *)

(** A digraph with no vertices is acyclic (the [forall] is vacuous). *)
Lemma acyclicb_empty (D : diGraphType) : #|D| = 0 -> acyclicb D.
Proof.
move=> /card0_eq D0; apply/forallP=> v.
by move: (D0 v); rewrite inE.
Qed.

(** ** Loops kill dicolourability at every k *)

(** If some vertex carries a loop, [D] is not k-dicolourable for any k: the
    colour class of that vertex contains its loop, hence is not acyclic. *)
Lemma loop_not_dicolorable (D : diGraphType) (v : D) (k : nat) :
  v --> v -> ~~ dicolorableb D k.
Proof.
move=> vv; apply/existsPn=> col; apply/forallPn.
exists (col v).
have vin : v \in [set u | col u == col v] by rewrite inE eqxx.
pose v' : induced_digraph [set u | col u == col v] := exist _ v vin.
apply: (loop_not_acyclicb (v := v')).
by rewrite sub_arcE /=.
Qed.

(** ** dicolorableb D 1 = acyclicb D  (χ⃗ ≤ 1 iff acyclic) *)

(** With one colour, the unique colour class is all of [V(D)]; the induced
    digraph there is isomorphic to [D]. *)
Lemma induced_setT_dgiso {D : diGraphType} :
  dgiso (induced_digraph (setT : {set D})) D.
Proof.
exists val; split.
  apply: (Bijective (g := fun x => exist _ x (in_setT x))).
    by case=> x px /=; apply: val_inj.
  by move=> x.
by move=> u w; rewrite sub_arcE.
Qed.

Lemma dicolorableb1 (D : diGraphType) : dicolorableb D 1 = acyclicb D.
Proof.
apply/idP/idP.
- move=> /existsP[col /forallP ac].
  have := ac ord0.
  have -> : [set v | col v == ord0] = setT.
    apply/setP=> v; rewrite !inE.
    by apply/eqP; apply: val_inj; case: (col v) => -[].
  by rewrite (acyclicb_dgiso induced_setT_dgiso).
- move=> ac; apply/existsP.
  exists [ffun _ => ord0 : 'I_1]; apply/forallP=> i.
  rewrite (ord1 i).
  have -> : [set v | [ffun _ => ord0 : 'I_1] v == ord0] = (setT : {set D}).
    by apply/setP=> v; rewrite !inE ffunE eqxx.
  by rewrite (acyclicb_dgiso induced_setT_dgiso).
Qed.

(** ** Transitive tournament is acyclic: χ⃗(TTₙ) = 1 *)

(** [arc] in [TT n] forces [val] to strictly increase along any [path]. *)
Lemma path_arc_TT_mono n (x : TT n) (t : seq (TT n)) :
  path arc x t -> all (fun y : TT n => (x < y)%N) t.
Proof.
elim: t x => [|h t IH] x //=.
case/andP=> xh pht.
have xlth : (x < h)%N by move: xh; rewrite arcTTE.
rewrite xlth /=.
have := IH h pht.
by apply: sub_all => y hy; apply: leq_ltn_trans (ltnW xlth) hy.
Qed.

Lemma acyclicb_TT n : acyclicb (TT n : diGraphType).
Proof.
apply/forallP=> v; apply/forallP=> w; apply/implyP=> vw.
apply/negP=> /connectP[s pws lastE].
have := path_arc_TT_mono pws.
move=> /allP/(_ v).
have vin : v \in s.
  case: s lastE pws => [|h t] /=; last by move=> ->; rewrite mem_last.
  by move=> E _; move: vw; rewrite -E arcTTE ltnn.
move=> /(_ vin) wv.
by move: vw; rewrite arcTTE => /ltn_trans/(_ wv); rewrite ltnn.
Qed.

(** χ⃗(TTₙ) ≤ 1: the transitive tournament is 1-dicolourable. *)
Lemma dicolorableb_TT1 n : dicolorableb (TT n : diGraphType) 1.
Proof. by rewrite dicolorableb1 acyclicb_TT. Qed.

(** ** Oriented digraphs on ≤ 2 vertices are acyclic

    The general fact behind χ⃗(C₃) ≤ 2: each colour class of a 2-colouring of a
    3-vertex tournament has ≤ 2 vertices, and an oriented digraph (irreflexive,
    no digon) on ≤ 2 vertices has no directed cycle. *)
Lemma acyclicb_oriented_le2 (D : diGraphType) :
  (#|D| <= 2)%N ->
  (forall x : D, ~~ (x --> x)) ->
  (forall x y : D, x --> y -> ~~ (y --> x)) ->
  acyclicb D.
Proof.
move=> Dle2 irr nodigon.
apply/forallP=> v; apply/forallP=> w; apply/implyP=> vw.
apply/negP=> /connectP[s].
case/shortenP=> p pathp uniqp _ lastE.
(* p is a simple path from w ending at v; the closing arc v-->w plus the path
   would need ≥ 3 distinct vertices once p is long enough. *)
case: p pathp uniqp lastE => [|h t] /=.
  (* v = w: the arc v-->w is a loop, impossible (irreflexive). *)
  move=> _ _ wv; move: vw; rewrite wv.
  by rewrite (negbTE (irr w)).
case/andP=> wh pht uniqp lastE.
case: t pht uniqp lastE => [|h2 t2] /=.
  (* v = h, arcs w-->h and v-->w = h-->w: a digon, impossible. *)
  move=> _ _ hv; move: vw; rewrite hv => hw.
  by case/negP: (nodigon w h wh).
case/andP=> hh2 _.
case/and4P=> wNht hNh2t _ _ _lastE.
(* w, h, h2 are three distinct vertices ⟹ #|D| ≥ 3, contra #|D| ≤ 2. *)
have wNh : w != h by move: wNht; rewrite inE negb_or => /andP[].
have wNh2 : w != h2 by move: wNht; rewrite !inE !negb_or => /and3P[].
have hNh2 : h != h2 by move: hNh2t; rewrite inE negb_or => /andP[].
have : (3 <= #|D|)%N.
  pose f (i : 'I_3) : D := nth w [:: w; h; h2] i.
  have finj : injective f.
    rewrite /f; move=> i j.
    case: i j => -[|[|[|//]]] ip [[|[|[|//]]] jp] //= eq0;
      try by apply: val_inj.
    - by rewrite eq0 eqxx in wNh.
    - by rewrite eq0 eqxx in wNh2.
    - by rewrite -eq0 eqxx in wNh.
    - by rewrite eq0 eqxx in hNh2.
    - by rewrite -eq0 eqxx in wNh2.
    - by rewrite -eq0 eqxx in hNh2.
  by have := leq_card f finj; rewrite card_ord.
by rewrite ltnNge Dle2.
Qed.

(** ** The directed triangle C₃: χ⃗(C₃) = 2 *)

(** Zp arithmetic helpers for the directed triangle [C3 = 'Z_3]. *)
Lemma C3_three0 : (1 + 1 + 1 : C3) = 0.
Proof. by apply: val_inj. Qed.

Lemma C3_two_neq0 : (1 + 1 : C3) != 0.
Proof. by apply/negP=> /eqP/(congr1 val). Qed.

Lemma C3_neq_succ (x : C3) : x != x + 1.
Proof. by rewrite -subr_eq0 opprD addrA subrr add0r oppr_eq0 oner_neq0. Qed.

Lemma C3_neq_succ2 (x : C3) : x != x + (1 + 1).
Proof. by rewrite -subr_eq0 !opprD !addrA subrr add0r -opprD oppr_eq0 C3_two_neq0. Qed.

(** C₃ has the directed 3-cycle [x -> x+1 -> x+2 -> x] for every [x] (here
    realised at [x = 0]): [0 -> 1 -> 2 -> 0]. *)
Lemma C3_dicycle (x : C3) : dicycle [:: x; x + 1; x + 2].
Proof.
have e2 : (x + 2 = x + (1 + 1)) by rewrite -[2%R]/(1 + 1)%R.
rewrite /dicycle /= !arcC3E e2.
apply/and4P; split=> //.
- apply/and3P; split.
  + by rewrite eqxx.
  + by rewrite addrA.
  + by rewrite andbT -addrA C3_three0 addr0 eqxx.
- by rewrite !inE negb_or C3_neq_succ C3_neq_succ2.
- by rewrite inE addrA; apply: C3_neq_succ.
Qed.

(** So C₃ is NOT acyclic. *)
Lemma not_acyclicb_C3 : ~~ acyclicb (C3 : diGraphType).
Proof. exact: (dicycle_not_acyclicb (C3_dicycle 0)). Qed.

(** RED-FLAG probe: χ⃗(C₃) > 1. [dicolorableb C3 1] is NOT provable; we prove
    its negation. If this failed (or [dicolorableb C3 1] proved), χ⃗ would be
    broken. *)
Lemma not_dicolorableb_C3_1 : ~~ dicolorableb (C3 : diGraphType) 1.
Proof. by rewrite dicolorableb1 not_acyclicb_C3. Qed.

(** C₃ is oriented: irreflexive and digon-free (it is a tournament). *)
Lemma C3_irr (x : C3) : ~~ (x --> x).
Proof. by rewrite arcC3E; case: x => -[|[|[|//]]] ?. Qed.

Lemma C3_nodigon (x y : C3) : x --> y -> ~~ (y --> x).
Proof. by case: x y => -[|[|[|//]]] ? [[|[|[|//]]] ?]. Qed.

(** χ⃗(C₃) ≤ 2: the directed triangle IS 2-dicolourable. Colour [2 -> 1],
    everything else [-> 0]; each class has ≤ 2 vertices, and the induced
    subdigraph there is oriented on ≤ 2 vertices, hence acyclic. *)
Lemma dicolorableb_C3_2 : dicolorableb (C3 : diGraphType) 2.
Proof.
apply/existsP.
exists [ffun v : C3 => if v == 2 then (1 : 'I_2) else (0 : 'I_2)].
apply/forallP=> i.
set col := [ffun v : C3 => if v == 2 then (1 : 'I_2) else (0 : 'I_2)].
set S := [set v | col v == i].
(* some vertex is missing from the colour class S, so #|S| < 3, i.e. ≤ 2 *)
have c0v2 : ((0 : C3) == 2) = false by apply/negbTE/eqP=> /(congr1 val).
have c0 : col (0 : C3) = 0 :> 'I_2 by rewrite ffunE c0v2.
have c2 : col (2 : C3) = 1 :> 'I_2 by rewrite ffunE eqxx.
have [z zNS] : exists z : C3, z \notin S.
  case: (boolP (i == 0 :> 'I_2)) => i0.
    by exists 2; rewrite inE -/col c2; move: i0 => /eqP ->.
  by exists 0; rewrite inE -/col c0 eq_sym.
apply: acyclicb_oriented_le2.
- rewrite card_sig.
  have SsubT : S \subset [set: C3] :\ z.
    apply/subsetP=> x xS; rewrite !inE andbT.
    by apply: contraNneq zNS => <-.
  apply: leq_trans (subset_leq_card SsubT) _.
  have card2 : #|[set: C3] :\ z| = 2.
    have h : #|[set: C3]| = (1 + #|[set: C3] :\ z|)%N by rewrite (cardsD1 z) inE.
    have e3 : #|[set: C3]| = 3 by rewrite cardsT card_ord.
    by move: h; rewrite e3 add1n; case.
  by rewrite card2.
- by move=> x; rewrite sub_arcE; exact: C3_irr.
- by move=> x y; rewrite !sub_arcE; exact: C3_nodigon.
Qed.

(** ** Monotonicity: more colours never hurt *)

(** [dicolorableb D k -> dicolorableb D k.+1]: widen the colour codomain; the
    used classes are unchanged, the new colour [k] is empty hence acyclic. *)
Lemma dicolorableb_monoS (D : diGraphType) (k : nat) :
  dicolorableb D k -> dicolorableb D k.+1.
Proof.
move=> /existsP[col /forallP colac].
apply/existsP; exists [ffun v => widen_ord (leqnSn k) (col v)]; apply/forallP=> i.
case: (ltnP i k) => [ik|ki].
  have -> : [set v | [ffun v0 => widen_ord (leqnSn k) (col v0)] v == i]
          = [set v | col v == Ordinal ik].
    by apply/setP=> v; rewrite !inE ffunE -!val_eqE /=.
  exact: (colac (Ordinal ik)).
have -> : [set v | [ffun v0 => widen_ord (leqnSn k) (col v0)] v == i] = set0.
  apply/setP=> v; rewrite !inE ffunE -val_eqE /=.
  by rewrite ltn_eqF // (leq_trans (ltn_ord (col v)) ki).
apply: acyclicb_empty.
by rewrite card_sig cards0.
Qed.

(** A sanity check that the [dichromatic_bounded] wrapper is satisfiable: the
    class of acyclic digraphs is χ⃗-bounded (by the constant 1). *)
Lemma dichromatic_bounded_acyclic :
  dichromatic_bounded (fun D : diGraphType => acyclicb D).
Proof. by exists 1 => D Dac; rewrite dicolorableb1. Qed.
