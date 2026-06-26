(** * Digraph.dipath — directed simple paths, the longest-path length ℓ(D),
      and the path-surgery kit

    Dossier items M-ℓ, K-A, K-Ext, K-D and the surgery kit (CK3 plan, M9).
    Everything in this file holds for ARBITRARY finite digraphs — no
    orientedness, no degree hypotheses (Decision D12).

    Design (D8 note): we build directly on MathComp's [path]/[cycle]/[next]
    seq library rather than on graph-theory's [pathp]/[upath] wrappers: the
    surgery needed here (cycles as seqs, [rot]/[next]/[prev], longest-path
    maxima) lives below graph-theory's layer, whose substantial machinery
    (the dependent [Path] type) targets connectivity, not extremal paths.
    This is the fallback priced into D8.

    Conventions (dossier §0): a directed simple path is a pair (x, s) with
    [dipath x s = path arc x s && uniq (x :: s)]; its LENGTH is [size s] =
    the number of ARCS; vertices are [x :: s]. A directed cycle is a seq [c]
    with [dicycle c = [&& ~~ nilp c, cycle arc c & uniq c]]; its length is
    [size c] (= #arcs = #vertices). [ℓ(D) = ell D] is the maximum length of
    a path; [ell D = 0] when D is empty. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DiPathDef.
Variable D : diGraphType.
Implicit Types (x y z w : D) (s c : seq D).

(** ** Directed simple paths *)

Definition dipath x s := path arc x s && uniq (x :: s).

Lemma dipath_path x s : dipath x s -> path arc x s.
Proof. by case/andP. Qed.

Lemma dipath_uniq x s : dipath x s -> uniq (x :: s).
Proof. by case/andP. Qed.

Lemma dipath_nil x : dipath x [::].
Proof. by []. Qed.

Lemma dipath_rcons x s w :
  dipath x (rcons s w) =
    [&& dipath x s, last x s --> w & w \notin x :: s].
Proof.
rewrite /dipath rcons_path -rcons_cons rcons_uniq.
by case: (path arc x s); case: (last x s --> w);
   case: (w \notin x :: s); case: (uniq (x :: s)).
Qed.

Lemma cat_dipath x s y t :
  dipath x s -> last x s --> y -> dipath y t ->
  ~~ has (mem (x :: s)) (y :: t) -> dipath x (s ++ y :: t).
Proof.
case/andP=> ps us ay /andP[pt ut] dis.
rewrite /dipath cat_path /= ay pt ps /=.
have U : uniq ((x :: s) ++ (y :: t)) by rewrite cat_uniq us ut dis.
by move: U; rewrite cat_cons cons_uniq.
Qed.

(** Continuation form: append a path that starts AT the endpoint. *)
Lemma cat_dipath_cont x s t :
  dipath x s -> dipath (last x s) t -> ~~ has (mem (x :: s)) t ->
  dipath x (s ++ t).
Proof.
case/andP=> ps us /andP[pt /= /andP[_ ut]] dis.
rewrite /dipath cat_path ps pt /=.
move: us => /= /andP[xNs us].
rewrite mem_cat negb_or xNs /=.
have xNt : x \notin t.
  apply: contra dis => xt; apply/hasP.
  by exists x => //=; rewrite mem_head.
rewrite xNt /= cat_uniq us ut andbT /=.
apply: contra dis => /hasP[w wt wsM].
by apply/hasP; exists w => //=; rewrite inE wsM orbT.
Qed.

Lemma dipath_cons x y t : dipath x (y :: t) -> (x --> y) /\ dipath y t.
Proof.
case/andP=> /= /andP[axy pt] /and3P[_ yNt ut].
by split; rewrite // /dipath pt /= yNt ut.
Qed.

Lemma dipath_drop x s j : dipath x s -> j < size s ->
  dipath (nth x s j) (drop j.+1 s).
Proof.
case/andP=> ps us jlt.
have lt : last x (take j.+1 s) = nth x s j.
  by rewrite (take_nth x jlt) last_rcons.
move: ps; rewrite -{1}(cat_take_drop j.+1 s) cat_path lt => /andP[_ pd].
rewrite /dipath pd /=.
move: us => /= /andP[_ us].
move: (us); rewrite -{1}(cat_take_drop j.+1 s) cat_uniq => /and3P[_ nh ud].
rewrite ud andbT.
apply: contra nh => nthd; apply/hasP.
exists (nth x s j) => //=.
by rewrite (take_nth x jlt) mem_rcons mem_head.
Qed.

Lemma last_take x s j : j < size s -> last x (take j.+1 s) = nth x s j.
Proof. by move=> jlt; rewrite (take_nth x jlt) last_rcons. Qed.

Lemma last_drop x s j : j < size s ->
  last (nth x s j) (drop j.+1 s) = last x s.
Proof.
move=> jlt.
rewrite -{3}(cat_take_drop j.+1 s) last_cat.
by rewrite (last_take x jlt).
Qed.

(** Endpoint of a prefix, on the (x :: s) indexing. *)
Lemma take_path_last x s j : j <= size s ->
  last x (take j s) = nth x (x :: s) j.
Proof.
case: j => [|j] jle; first by rewrite take0.
exact: last_take.
Qed.

Lemma dipath_take x s n : dipath x s -> dipath x (take n s).
Proof.
case/andP=> ps us; rewrite /dipath.
rewrite -{1}(cat_take_drop n s) cat_path in ps; case/andP: ps => -> _ /=.
by move: us; rewrite -{1}(cat_take_drop n s) -cat_cons cat_uniq; case/andP.
Qed.

(** The i-th vertex of the path (x, s), i ranging over 0..size s. *)
Lemma dipath_arc_nth x s i : path arc x s -> i < size s ->
  nth x (x :: s) i --> nth x (x :: s) i.+1.
Proof. by move=> /pathP h ilt; have := h x i ilt. Qed.

Lemma dipath_size x s : dipath x s -> size s < #|D|.
Proof.
case/andP=> _ us; have /card_uniqP cardE := us.
by have := max_card (mem (x :: s)); rewrite cardE /=.
Qed.

(** ** The longest-path length ℓ(D) *)

Definition has_dipath k := [exists x : D, exists t : k.-tuple D, dipath x t].

Lemma has_dipathP k :
  reflect (exists x s, dipath x s /\ size s = k) (has_dipath k).
Proof.
apply: (iffP existsP) => [[x /existsP[t pt]]|[x [s [ps sk]]]].
  by exists x, t; split; rewrite ?size_tuple.
exists x; apply/existsP.
by exists (tcast sk (in_tuple s)); rewrite val_tcast /=.
Qed.

Definition ell := \max_(k < #|D| | has_dipath k) (k : nat).

Lemma ell_max x s : dipath x s -> size s <= ell.
Proof.
move=> ps.
have slt : size s < #|D| by exact: dipath_size ps.
pose o := Ordinal slt.
have hk : has_dipath o by apply/has_dipathP; exists x, s.
exact: (bigmax_sup o).
Qed.

Lemma ellP : 0 < #|D| -> exists x s, dipath x s /\ size s = ell.
Proof.
move=> n_gt0; have /card_gt0P[x0 _] := n_gt0.
have h0 : has_dipath (Ordinal n_gt0 : 'I_#|D|).
  by apply/has_dipathP; exists x0, [::].
rewrite /ell (bigmax_eq_arg (F := fun k : 'I_#|D| => (k : nat)) _ h0) //.
case: arg_maxnP => //= i hi _.
by case/has_dipathP: hi => x [s [ps sk]]; exists x, s.
Qed.

(** ** K-A: out-neighbours of the endpoint of a maximum path lie on it *)

Lemma maxpath_endclosure x s w :
  dipath x s -> size s = ell -> last x s --> w -> w \in x :: s.
Proof.
move=> ps sE aw; case: (boolP (w \in x :: s)) => // wN; exfalso.
have pr : dipath x (rcons s w) by rewrite dipath_rcons ps aw wN.
by have := ell_max pr; rewrite size_rcons sE ltnn.
Qed.

(** ** End-maximal paths and K-Ext *)

Definition endmax x s :=
  dipath x s && [forall w : D, (last x s --> w) ==> (w \in x :: s)].

Lemma endmax_closure x s w :
  endmax x s -> last x s --> w -> w \in x :: s.
Proof. by case/andP=> _ /forallP/(_ w)/implyP h /h. Qed.

Lemma endmax_dipath x s : endmax x s -> dipath x s.
Proof. by case/andP. Qed.

(** K-Ext: every vertex starts some end-maximal path. *)
Lemma endmax_ex x : exists s, endmax x s.
Proof.
have n_gt0 : 0 < #|D| by apply/card_gt0P; exists x.
pose hx (k : nat) := [exists t : k.-tuple D, dipath x t].
have h0 : hx (Ordinal n_gt0 : 'I_#|D|) by apply/existsP; exists (in_tuple [::]).
pose kx := \max_(k < #|D| | hx k) (k : nat).
have kx_max y t : dipath x t -> size t <= kx.
  move=> pt; have slt : size t < #|D| by exact: dipath_size pt.
  have hk : hx (Ordinal slt).
    by apply/existsP; exists (tcast (erefl _) (in_tuple t)).
  exact: (bigmax_sup (Ordinal slt)).
have [s [ps sk]] : exists s, dipath x s /\ size s = kx.
  rewrite /kx (bigmax_eq_arg (F := fun k : 'I_#|D| => (k : nat)) _ h0) //.
  case: arg_maxnP => //= i /existsP[t pt] _.
  by exists t; split; rewrite ?size_tuple.
exists s; rewrite /endmax ps /=.
apply/forallP=> w; apply/implyP=> aw.
case: (boolP (w \in x :: s)) => // wN; exfalso.
have pr : dipath x (rcons s w) by rewrite dipath_rcons ps aw wN.
by have := kx_max x _ pr; rewrite size_rcons sk ltnn.
Qed.

(** ** Directed cycles as seqs *)

Definition dicycle c := [&& ~~ nilp c, cycle arc c & uniq c].

Lemma dicycle_rot n c : dicycle (rot n c) = dicycle c.
Proof. by rewrite /dicycle rot_cycle rot_uniq /nilp size_rot. Qed.

(** The closing/cyclic arcs: every cycle vertex beats its [next]. *)
Lemma dicycle_next c z : dicycle c -> z \in c -> z --> next c z.
Proof. by case/and3P=> _ cyc _; exact: next_cycle. Qed.

Lemma dicycle_prev c z : dicycle c -> z \in c -> prev c z --> z.
Proof. by case/and3P=> _ cyc _; exact: prev_cycle. Qed.

(** Unrolling: a cycle yields a path from any of its vertices through all
    of it, ending at the predecessor (with the closing arc back). *)
Lemma dicycle_unroll z c : dicycle c -> z \in c ->
  exists s, [/\ dipath z s, size s = (size c).-1, (z :: s) =i c,
              last z s --> z & last z s = prev c z].
Proof.
move=> dc zc.
case/rot_to: (zc) => i s rotE.
have dc' : dicycle (z :: s) by rewrite -rotE dicycle_rot.
case/and3P: dc' => _ cyc un.
move: cyc; rewrite /= rcons_path => /andP[ps az].
have uc : uniq c by case/and3P: dc.
have lastE : last z s = prev c z.
  rewrite -(prev_rot i uc) rotE.
  have zNs : z \notin s by case/andP: un.
  have helper t y : z \notin t -> prev_at z z y t = last y t.
    elim: t y => [|h t IH] y /=; first by rewrite eqxx.
    rewrite inE negb_or => /andP[zDh zNt].
    by rewrite (negbTE zDh) IH.
  by rewrite /prev helper.
exists s; split=> //.
- by rewrite /dipath ps.
- by rewrite -(size_rot i c) rotE.
- by move=> w; rewrite -rotE mem_rot.
Qed.

(** Cycle from a path suffix plus a back-arc from the endpoint. *)
Lemma dicycle_suffix x s i : dipath x s -> i < size (x :: s) ->
  last x s --> nth x (x :: s) i -> dicycle (drop i (x :: s)).
Proof.
case/andP=> ps us.
case: i => [|j] ilt aw.
  rewrite drop0 /dicycle /= rcons_path ps /=.
  by move: aw => /= ->; move: us => /= /andP[-> ->].
rewrite -[drop j.+1 (x :: s)]/(drop j s) /dicycle.
have ujs : uniq (drop j s) by case/andP: us => _ us'; exact: drop_uniq.
have jlt : j < size s by [].
case Edrop: (drop j s) => [|h t].
  by move: jlt; rewrite -subn_gt0 -size_drop Edrop.
have hE : h = nth x s j by rewrite -[j]addn0 -nth_drop Edrop.
have lastE : last x s = last h t.
  by rewrite -(cat_take_drop j s) last_cat Edrop.
move: ps; rewrite -(cat_take_drop j s) cat_path Edrop.
move=> /andP[_ /= /andP[_ pht]].
rewrite /= rcons_path pht /= -lastE.
have -> : last x s --> h by rewrite hE; exact: aw.
by rewrite Edrop in ujs; move: ujs => /= /andP[-> ->].
Qed.

End DiPathDef.

Arguments ell D : clear implicits.

(** [prev] of the head of a uniq seq is its last element (eqType-level
    helper for cycle predecessor reasoning). *)
Lemma prev_head (T : eqType) (c : seq T) (y : T) :
  uniq c -> 0 < size c -> prev c (head y c) = last y c.
Proof.
case: c => //= h t /andP[hNt _] _.
rewrite /prev.
have helper : forall t' w, h \notin t' -> prev_at h h w t' = last w t'.
  elim=> [|h2 t' IH] w /=; first by rewrite eqxx.
  rewrite inE negb_or => /andP[hDh2 hNt'].
  by rewrite (negbTE hDh2) IH.
exact: helper.
Qed.

(** ** M-ℓ: ℓ is monotone under injective arc-preserving embeddings *)

Lemma dipath_map (D1 D2 : diGraphType) (f : D1 -> D2) (x : D1) (s : seq D1) :
  injective f -> (forall u v, u --> v -> f u --> f v) ->
  dipath x s -> dipath (f x) (map f s).
Proof.
move=> inj_f hom /andP[ps us].
rewrite /dipath -map_cons map_inj_uniq // us andbT.
elim: s x {us} ps => [|y t IH] x //= /andP[axy pt].
by rewrite (hom _ _ axy) IH.
Qed.

Lemma ell_embed (D1 D2 : diGraphType) (f : D1 -> D2) :
  injective f -> (forall u v, u --> v -> f u --> f v) ->
  ell D1 <= ell D2.
Proof.
move=> inj_f hom.
case: (posnP #|D1|) => [n0|n_gt0].
  apply/bigmax_leqP => k _; case: k => m mlt /=.
  by rewrite n0 ltn0 in mlt.
have [x [s [ps sE]]] := ellP n_gt0.
rewrite -sE -(size_map f s).
exact: ell_max (dipath_map inj_f hom ps).
Qed.

(** The two instances used by the reduction R: arc-sub-relations and
    induced subgraphs. *)

Lemma ell_outsel (D : diGraphType) (f : D -> {set D}) :
  ell (outsel f) <= ell D.
Proof.
apply: (ell_embed (f := fun x : outsel f => (x : D))) => // u v.
exact: outsel_arc_sub.
Qed.

Lemma ell_induced (D : diGraphType) (A : {set D}) :
  ell (induced_digraph A) <= ell D.
Proof.
apply: (ell_embed (f := fun x : induced_digraph A => val x)).
  exact: val_inj.
by move=> u v; rewrite sub_arcE.
Qed.
