(** * Digraph.domination — directed domination and dom(T) ≤ ω̄(T)

    A set [X] *dominates* a tournament when every vertex outside [X] is
    beaten by some member of [X]; [domnum T] is the least size of a
    dominating set. (This is the *directed* notion — graph-theory's [dom.v]
    is undirected-only, Decision D3 — though we reuse nothing from it here.)

    The marquee theorem is the paper's Property 3.2: [domnum T <= ω̄(T)].
    Proof: fix an optimal order [p]. Greedily pick [x1] := the ≺ₚ-minimum
    vertex, discard everything [x1] beats, recurse on the rest
    ([greedy_clique_dom]). Each later pick beats all earlier ones (it was
    never dominated) yet sits ≺ₚ-after them (minima of shrinking sets), so
    the picks form a *backedge clique* — hence at most ω̄(T) of them — and by
    construction they dominate everything. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Domination.
Variable T : tournament.

Definition dominatesb (X : {set T}) : bool :=
  [forall v : T, (v \in X) || [exists x in X, x --> v]].

Lemma dominatesbP (X : {set T}) :
  reflect (forall v, v \notin X -> exists2 x, x \in X & x --> v)
          (dominatesb X).
Proof.
apply: (iffP forallP) => [h v vNX | h v].
- have := h v; rewrite (negbTE vNX) /= => /existsP[x /andP[xX xv]].
  by exists x.
- case e: (v \in X) => //=.
  have [x xX xv] := h v (negbT e).
  by apply/existsP; exists x; rewrite xX xv.
Qed.

Lemma dominatesb_setT : dominatesb [set: T].
Proof. by apply/forallP=> v; rewrite inE. Qed.

Definition domnum : nat := #|[arg min_(X < [set: T] | dominatesb X) #|X|]|.

Lemma domnum_min (X : {set T}) : dominatesb X -> domnum <= #|X|.
Proof.
rewrite /domnum; case: arg_minnP => [|Y _ Ymin]; first exact: dominatesb_setT.
exact: Ymin.
Qed.

Lemma domnum_witness : exists2 X : {set T}, dominatesb X & domnum = #|X|.
Proof.
rewrite /domnum; case: arg_minnP => [|Y Ydom _]; first exact: dominatesb_setT.
by exists Y.
Qed.

(** The greedy chain: inside any [A] there is a subset that dominates [A]
    and is a clique of the backedge graph of [p] (the ≺ₚ-minimum first,
    every later pick beating — and sitting ≺ₚ-after — all earlier ones). *)
Lemma greedy_clique_dom (p : {perm T}) (n : nat) (A : {set T}) : #|A| <= n ->
  exists X : {set T},
    [/\ X \subset A,
        {in A, forall v, v \notin X -> exists2 x, x \in X & x --> v}
      & {in X &, forall a b : T,
           a != b -> ((a : backedge p) -- (b : backedge p))}].
Proof.
elim: n A => [|n IHn] A cardA.
  exists set0; split; rewrite ?sub0set //.
    move: cardA; rewrite leqn0 cards_eq0 => /eqP-> v.
    by rewrite inE.
  by move=> a; rewrite inE.
case: (eqVneq A set0) => [->|Anon].
  exists set0; split; rewrite ?sub0set //.
  - by move=> v; rewrite inE.
  - by move=> a; rewrite inE.
have [x0 x0A] := set0Pn _ Anon.
have [x1 x1A x1min] := arg_minnP (fun x : T => val (enum_rank (p x))) x0A.
pose A' := [set v in A | ~~ (x1 --> v) & (v != x1)].
have A'subD : A' \subset A :\ x1.
  by apply/subsetP=> v; rewrite !inE => /and3P[-> _ ->].
have cardA' : #|A'| <= n.
  rewrite (leq_trans (subset_leq_card A'subD)) //.
  have x1A' : x1 \in A := x1A.
  by move: cardA; rewrite (cardsD1 x1) x1A' add1n ltnS.
have [X' [X'sub X'dom X'cl]] := IHn _ cardA'.
exists (x1 |: X'); split.
- rewrite subUset sub1set (x1A : x1 \in A) /=.
  apply: subset_trans X'sub _.
  by apply/subsetP=> v; rewrite inE => /and3P[].
- move=> v vA; rewrite !inE negb_or => /andP[vNx1 vNX'].
  case e: (x1 --> v).
    by exists x1; rewrite ?setU11.
  have vA' : v \in A' by rewrite !inE vA e vNx1.
  have [x xX' xv] := X'dom v vA' vNX'.
  by exists x; rewrite ?inE ?xX' ?orbT.
have x1edge (b : T) : b \in X' -> ((x1 : backedge p) -- (b : backedge p)).
  move=> bX'; have := subsetP X'sub _ bX'; rewrite !inE => /and3P[bA Nx1b bNx1].
  have arcb : b --> x1 by rewrite (arcNarc bNx1).
  have ltpx1b : ltp p x1 b.
    rewrite /ltp ltn_neqAle x1min ?andbT //.
    by rewrite val_eqE (inj_eq enum_rank_inj) (inj_eq perm_inj) eq_sym bNx1.
  by rewrite backedgeE ltpx1b arcb.
move=> a b /setU1P[->|aX'] /setU1P[->|bX'] // aNb.
- by rewrite eqxx in aNb.
- exact: x1edge bX'.
- by rewrite sg_sym; exact: x1edge aX'.
- exact: X'cl.
Qed.

(** Paper Property 3.2 — the lower-bound engine for ω̄. *)
Theorem domnum_le_omegabar : domnum <= ω̄(T).
Proof.
have [p obp] := omegabar_witness T.
have [X [_ Xdom Xcl]] := greedy_clique_dom p (leqnn #|[set: T]|).
have Xdom' : dominatesb X.
  by apply/dominatesbP=> v vNX; apply: (Xdom v (in_setT v) vNX).
apply: leq_trans (domnum_min Xdom') _.
rewrite obp /omegab_at.
apply: clique_bound; rewrite inE subsetT /=.
by apply/cliqueP=> a b aX bX aNb; apply: Xcl.
Qed.

End Domination.
