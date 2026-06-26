(** * Digraph.strong — strong connectivity, the sink-SCC trick, and the
      out-regular reduction

    Dossier items S1, S2, R, K-a1 and K-10 (CK3 plan, M10). Everything up
    to [reduction] holds for ARBITRARY finite digraphs (Decision D12);
    only the reduction itself asks for orientedness (through O1/O2).

    - [strongb]: boolean strong connectivity via fingraph's [connect];
    - S1: forward-closed sets, reachable sets, and the sink trick — the
      reachable set of a vertex minimizing |R(x)| is closed and strongly
      connected inside ([sink_exists]); induced subgraphs on closed sets
      keep their out-degrees ([outdeg_closed]) and inherit strongness
      ([strongb_induced_closed]);
    - S2: an arc crosses into any reachable target set ([connect_cross]);
    - R: the composed reduction — any nonempty oriented digraph with
      δ⁺ ≥ k contains (as an induced subgraph of an out-selection) a
      strong, k-outregular oriented digraph H with ℓ(H) ≤ ℓ(D) and
      |H| ≥ 2k+1 ([reduction]);
    - K-a1: on a strong digraph that is strictly larger than a maximum
      path, the endpoint of such a path does not beat its head
      ([maxpath_no_loopback]);
    - K-10: two disjoint cycles in a strong digraph force
      ℓ ≥ |C₁| + |C₂| − 1 ([disjoint_cycles_path]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Strong.
Variable D : diGraphType.
Implicit Types (x y z : D) (A W : {set D}).

Definition strongb := [forall x : D, forall y : D, connect arc x y].

Lemma strongP : reflect (forall x y, connect arc x y) strongb.
Proof. by apply: (iffP forallP) => h x; [exact/forallP | apply/forallP]. Qed.

(** ** S1: forward-closed sets and the sink trick *)

Definition arc_closed A := forall u v, u --> v -> u \in A -> v \in A.

Lemma closed_connect A x y :
  arc_closed A -> connect arc x y -> x \in A -> y \in A.
Proof.
move=> Acl /connectP[p pp ->] xA.
elim: p x pp xA => [|h t IH] x //= /andP[axh pt] xA.
exact: IH (Acl _ _ axh xA).
Qed.

Definition rset x := [set y | connect arc x y].

Lemma rset_id x : x \in rset x.
Proof. by rewrite inE connect0. Qed.

Lemma rset_closed x : arc_closed (rset x).
Proof.
move=> u v auv; rewrite !inE => cxu.
exact: connect_trans cxu (connect1 auv).
Qed.

Lemma rset_trans x y : y \in rset x -> rset y \subset rset x.
Proof.
rewrite inE => cxy; apply/subsetP=> z; rewrite !inE => cyz.
exact: connect_trans cxy cyz.
Qed.

(** The sink trick: a reachable set of minimum size is closed and strongly
    connected inside. *)
Lemma sink_exists : 0 < #|D| ->
  exists W, [/\ W != set0, arc_closed W
             & forall y z, y \in W -> z \in W -> connect arc y z].
Proof.
move=> /card_gt0P[x0 _].
pose xm := [arg min_(x < x0) #|rset x|].
exists (rset xm); split.
- by apply/set0Pn; exists xm; exact: rset_id.
- exact: rset_closed.
- move=> y z; rewrite !inE => cy cz.
  have rE : rset y = rset xm.
    apply/eqP; rewrite eqEcard rset_trans ?inE //=.
    by rewrite /xm; case: arg_minnP => // i _; apply.
  have : z \in rset y by rewrite rE inE.
  by rewrite inE.
Qed.

(** Closed sets keep out-degrees in the induced subgraph. *)
Lemma outdeg_closed A (u : induced_digraph A) :
  arc_closed A -> outdeg u = outdeg (val u).
Proof.
move=> Acl; rewrite outdeg_induced /outdeg_in /outdeg.
apply: eq_card => w; rewrite !inE andb_idl //.
by move=> aw; exact: Acl aw (valP u).
Qed.

(** Connectivity relativizes to closed sets. *)
Lemma connect_induced_closed A (u v : induced_digraph A) :
  arc_closed A -> connect arc (val u) (val v) -> connect arc u v.
Proof.
move=> Acl /connectP[p pp lastE].
elim: p u pp lastE => [|h t IH] u /=.
  by move=> _ lastE; have -> : u = v by apply: val_inj.
case/andP=> auh pt lastE.
have hA : h \in A by exact: Acl auh (valP u).
apply: connect_trans (connect1 _) (IH (Sub h hA) _ _).
- by rewrite sub_arcE SubK.
- by rewrite SubK.
- by rewrite SubK.
Qed.

(** ** S2: cut crossing *)

Lemma connect_cross A x y : connect arc x y -> x \notin A -> y \in A ->
  exists u v, [/\ u \notin A, v \in A & u --> v].
Proof.
case/connectP=> p pp lastE xNA yA.
elim: p x pp lastE xNA => [|h t IH] x /=.
  by move=> _ yE xNA; rewrite -yE yA in xNA.
case/andP=> axh pt yE xNA.
case hA : (h \in A); first by exists x, h.
by apply: IH pt yE _; rewrite hA.
Qed.

(** ** K-a1: no loopback arc at a maximum path's endpoint *)

Lemma maxpath_no_loopback x s :
  strongb -> dipath x s -> size s = ell D -> (size s).+2 <= #|D| ->
  last x s --> x = false.
Proof.
move=> /strongP str ps sE nlt.
case ax : (last x s --> x) => //; exfalso.
have dc : dicycle (x :: s).
  by have := dicycle_suffix ps (i := 0) isT ax; rewrite drop0.
have [w wNc] : exists w, w \notin x :: s.
  case: (boolP [forall w : D, w \in x :: s]) => [/forallP allin|]; last first.
    by rewrite negb_forall => /existsP[w wn]; exists w.
  have : #|D| <= size (x :: s).
    rewrite -(card_uniqP (dipath_uniq ps)).
    by apply: subset_leq_card; apply/subsetP=> z _; rewrite allin.
  by move=> le; have := leq_ltn_trans le nlt; rewrite /= ltnn.
have [u [v [uNc vc auv]]] : exists u v,
    [/\ u \notin [set z in x :: s], v \in [set z in x :: s] & u --> v].
  apply: (connect_cross (x := w) (y := x)); rewrite ?inE ?mem_head //.
  by rewrite eqxx.
have vc' : v \in x :: s by move: vc; rewrite inE.
have uNc' : u \notin x :: s by move: uNc; rewrite inE.
have [t [pt szt cov axt lastE]] := dicycle_unroll dc vc'.
have pu : dipath u (v :: t).
  rewrite /dipath /= auv /=.
  case/andP: pt => -> /= /andP[-> ->]; rewrite !andbT.
  by rewrite cov.
have := ell_max pu.
by rewrite /= szt /= sE ltnn.
Qed.

(** ** K-10: disjoint cycles force long paths *)

Lemma disjoint_cycles_path (c1 c2 : seq D) :
  strongb -> dicycle c1 -> dicycle c2 -> [disjoint c1 & c2] ->
  size c1 + size c2 - 1 <= ell D.
Proof.
move=> /strongP str dc1 dc2 dis.
have c1n0 : 0 < size c1 by case/and3P: dc1 => n1 _ _; rewrite lt0n -/(nilp c1).
have c2n0 : 0 < size c2 by case/and3P: dc2 => n2 _ _; rewrite lt0n -/(nilp c2).
have [u1 u1c] : exists u1, u1 \in c1.
  by case: c1 c1n0 {dc1 dis} => // h t _; exists h; rewrite mem_head.
have [u2 u2c] : exists u2, u2 \in c2.
  by case: c2 c2n0 {dc2 dis} => // h t _; exists h; rewrite mem_head.
pose Pk (k : nat) :=
  [exists y : D, exists t : k.-tuple D,
    [&& dipath y t, y \in c1 & last y (t : seq D) \in c2]].
have exP : exists k, Pk k.
  have := str u1 u2; case/connectP=> p0 pp0 lp0.
  move: lp0; case: (shortenP pp0) => p' pp' up' _ lp'.
  have dp' : dipath u1 p' by rewrite /dipath pp' up'.
  exists (size p'); apply/existsP; exists u1; apply/existsP.
  exists (tcast (erefl _) (in_tuple p')) => /=.
  by rewrite dp' u1c -lp' u2c.
case: (ex_minnP exP) => k0 Pk0 kmin.
case/existsP: Pk0 => y /existsP[tt /and3P[pt yc1 lc2]].
set ts := (tt : seq D) in pt lc2.
have szts : size ts = k0 by rewrite /ts size_tuple.
have tn0 : 0 < size ts.
  case: (ts) lc2 => //= lc2'.
  by have := disjointFr dis yc1; rewrite lc2'.
have noC1 : forall j, j < size ts -> nth y ts j \notin c1.
  move=> j jlt; apply/negP=> inc1.
  have pd := dipath_drop pt jlt.
  have ld : last (nth y ts j) (drop j.+1 ts) = last y ts by exact: last_drop.
  have : Pk (size (drop j.+1 ts)).
    apply/existsP; exists (nth y ts j); apply/existsP.
    exists (tcast (erefl _) (in_tuple (drop j.+1 ts))) => /=.
    by rewrite pd inc1 ld lc2.
  move/kmin; rewrite size_drop szts => le.
  have lt : k0 - j.+1 < k0 by rewrite ltn_subrL /= -szts tn0.
  by have := leq_ltn_trans le lt; rewrite ltnn.
have noC2 : forall j, j.+1 < size ts -> nth y ts j \notin c2.
  move=> j jlt; apply/negP=> inc2.
  have pt' : dipath y (take j.+1 ts) by exact: dipath_take.
  have lt' : last y (take j.+1 ts) = nth y ts j.
    by apply: last_take; exact: ltnW.
  have : Pk (size (take j.+1 ts)).
    apply/existsP; exists y; apply/existsP.
    exists (tcast (erefl _) (in_tuple (take j.+1 ts))) => /=.
    by rewrite pt' yc1 lt' inc2.
  move/kmin; rewrite size_take jlt => le.
  by have := leq_ltn_trans le jlt; rewrite szts ltnn.
have uc1 : uniq c1 by case/and3P: dc1.
have z1c : next c1 y \in c1 by rewrite mem_next.
have [s1 [p1 sz1 cov1 a1 l1E]] := dicycle_unroll dc1 z1c.
have l1y : last (next c1 y) s1 = y by rewrite l1E prev_next.
have memts : forall z, z \in ts -> exists2 j, j < size ts & nth y ts j = z.
  by move=> z /(nthP y)[j jlt <-]; exists j.
have glue1 : dipath (next c1 y) (s1 ++ ts).
  apply: cat_dipath_cont => //; first by rewrite l1y.
  apply/hasPn=> z /memts[j jlt <-] /=.
  by rewrite cov1; exact: noC1.
have lastg1 : last (next c1 y) (s1 ++ ts) = last y ts.
  by rewrite last_cat l1y.
have [s2 [p2 sz2 cov2 a2 l2E]] := dicycle_unroll dc2 lc2.
have glue2 : dipath (next c1 y) ((s1 ++ ts) ++ s2).
  apply: cat_dipath_cont => //; first by rewrite lastg1.
  apply/hasPn=> z zs2 /=.
  have zc2 : z \in c2 by rewrite -cov2 inE zs2 orbT.
  have zNlast : z != last y ts.
    apply: contraTneq zs2 => ->.
    by have /andP[h _] := dipath_uniq p2.
  rewrite -cat_cons mem_cat negb_or.
  apply/andP; split.
    rewrite cov1; apply/negP=> zc1.
    by have := disjointFr dis zc1; rewrite zc2.
  apply/negP=> /memts[j jlt njE].
  case: (ltngtP j.+1 (size ts)) => [jlt1|//|jE]; last 2 first.
  - by move=> h; have := leq_trans h jlt; rewrite ltnn.
  - move: zNlast; rewrite -njE (last_nth y) -jE.
    by rewrite -[nth y (y :: ts) j.+1]/(nth y ts j) eqxx.
  - by have := noC2 _ jlt1; rewrite njE zc2.
have := ell_max glue2.
rewrite !size_cat sz1 sz2 szts => le; apply: leq_trans le.
apply: leq_trans (_ : (size c1).-1 + 1 + (size c2).-1 <= _); last first.
  by rewrite leq_add2r leq_add2l -szts.
rewrite addn1 (prednK c1n0).
by rewrite -addnBA ?c2n0 // subn1.
Qed.

End Strong.

Arguments strongb D : clear implicits.

(** Strongness of the induced subgraph on a closed, internally connected
    set. *)
Lemma strongb_induced_closed (D : diGraphType) (W : {set D}) :
  arc_closed W ->
  (forall y z, y \in W -> z \in W -> connect arc y z) ->
  strongb (induced_digraph W).
Proof.
move=> Wcl Wconn; apply/strongP=> u v.
apply: connect_induced_closed => //.
by apply: Wconn; [exact: (valP u) | exact: (valP v)].
Qed.

(** ** R: the composed out-regular reduction (dossier item R) *)

Theorem reduction (O : orientedDigraph) (k : nat) :
  0 < #|O| -> (forall v : O, k <= outdeg v) ->
  exists W : {set outsel (@ksel O k)},
    [/\ 0 < #|induced_oriented W|,
        strongb (induced_oriented W),
        (forall v : induced_oriented W, outdeg v = k),
        ell (induced_oriented W) <= ell O
      & 2 * k + 1 <= #|induced_oriented W| ].
Proof.
move=> n0 dmin.
have n0' : 0 < #|{: outsel (@ksel O k)}| by exact: n0.
have [W [Wn0 Wcl Wconn]] := sink_exists n0'.
exists W.
have cardW : #|induced_oriented W| = #|W| by rewrite card_sig.
have outE : forall v : induced_oriented W, outdeg v = k.
  move=> v; rewrite (outdeg_closed v Wcl).
  exact: outsel_ksel_outdeg.
have hn0 : 0 < #|induced_oriented W| by rewrite cardW card_gt0.
split=> //.
- exact: strongb_induced_closed.
- apply: leq_trans (ell_induced _) _; exact: ell_outsel.
- exact: oriented_card hn0 (fun v => eq_leq (esym (outE v))).
Qed.
