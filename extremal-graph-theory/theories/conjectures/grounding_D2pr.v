(** * Extremal.conjectures.grounding_D2pr — grounding lemmas for milestone D2pr.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced in
    [D2pr.v].  For each genuinely new definition we record a satisfiable witness
    and/or at least one textbook identity (structural projections, symmetry,
    degenerate witnesses, nonnegativity of the counting expectations).  These are
    statement-validation lemmas, NOT the (open) conjectures themselves — every
    conjecture row stays statement-only in [D2pr.v].

    Primitives reused verbatim from GTBase.base / GraphTheory (χ, alpha, trunc_log,
    connect, …) are not re-grounded here. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Extremal.conjectures Require Import D2pr.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Shared vocabulary — [srel]/[mkG], [adjb], [edge2], [cyc_rel]/[cycle_graph] *)

(** [mkG]/[srel] identity: the edge relation of [mkG r] is exactly [srel r]. *)
Lemma mkG_edge (V:finType)(r:rel V)(x y:mkG r) : (x -- y) = srel r x y.
Proof. by []. Qed.

(** [adjb] is symmetric: [{x,y}] is a listed edge iff [{y,x}] is. *)
Lemma adjb_sym (V:finType)(E:{set {set V}}) : symmetric (adjb E).
Proof.
move=> x y; rewrite /adjb.
suff ->: [set x; y] = [set y; x] by [].
by apply/setP=> z; rewrite !inE orbC.
Qed.

(** [edge2] is inhabited by every genuine edge: [x -- y] gives the 2-subset edge. *)
Lemma edge2_edge (G:sgraph)(x y:G) : x -- y -> [set x; y] \in edge2 G.
Proof.
move=> xy; rewrite inE; apply/existsP; exists x; apply/existsP; exists y.
by rewrite xy eqxx.
Qed.

(** Textbook identity: every member of [edge2 G] is a genuine 2-subset. *)
Lemma valid_edges_edge2 (G:sgraph) : valid_edges (edge2 G).
Proof.
apply/forallP=> e; rewrite inE; apply/implyP=> /existsP[x] /existsP[y] /andP[xy /eqP->].
by rewrite cards2 (sg_edgeNeq xy).
Qed.

(** [cycle_graph 1] (the cycle on a single vertex) is edgeless. *)
Lemma cycle_graph1_no_edge (x y : cycle_graph 1) : (x -- y) = false.
Proof. by rewrite (ord1 x) (ord1 y) sg_irrefl. Qed.

(** ** Row 1 — [valid_edges], [regularb], [connectedb], [hamiltonianb] *)

(** [valid_edges] is satisfiable: the empty edge set is (vacuously) valid. *)
Lemma valid_edges0 (V:finType) : valid_edges (V:=V) set0.
Proof. by apply/forallP=> e; rewrite in_set0. Qed.

(** [regularb] is satisfiable: the empty edge set is 0-regular. *)
Lemma regularb0 (V:finType) : regularb (V:=V) set0 0.
Proof.
apply/forallP=> x; apply/eqP.
have ->: [set y : V | adjb set0 x y] = set0.
  by apply/setP=> y; rewrite !inE /adjb in_set0.
by rewrite cards0.
Qed.

(** [connectedb] is satisfiable: any edge set on a 1-vertex type is connected. *)
Lemma connectedb_I1 (E:{set {set 'I_1}}) : connectedb E.
Proof. by apply/forallP=> x; apply/forallP=> y; rewrite (ord1 x) (ord1 y) connect0. Qed.

(** Textbook introduction for [hamiltonianb]: any spanning [uniq] cycle witnesses
    Hamiltonicity. *)
Lemma hamiltonianbP (V:finType)(E:{set {set V}})(s:#|V|.-tuple V) :
  cycle (adjb E) s -> uniq s -> hamiltonianb E.
Proof. by move=> c u; apply/existsP; exists s; rewrite c u. Qed.

(** ** Row 2 — [Echi] *)

(** Textbook identity: the expected chromatic number of a random subgraph is
    nonnegative (a quotient of a sum of nonnegative colour counts by a positive
    power of two). *)
Lemma Echi_ge0 (G:sgraph) : (0 <= Echi G)%R.
Proof.
rewrite /Echi; apply: divr_ge0; last by rewrite ler0z exprz_ge0.
by apply: sumr_ge0 => S _; rewrite ler0z.
Qed.

(** ** Row 3 — [strong_power] *)

(** The 0-th strong power is a single-vertex (the empty tuple) loopless graph. *)
Lemma strong_power0_no_edge (G:sgraph)(x y:strong_power G 0) : (x -- y) = false.
Proof.
rewrite mkG_edge /srel.
have e : x = y by apply/ffunP; case.
by rewrite e eqxx.
Qed.

(** ** Row 4 — [cpts], [forestb] *)

(** [cpts] on the empty vertex type is 0 (no components). *)
Lemma cpts_I0 (S:{set {set 'I_0}}) : cpts S = 0.
Proof.
have e0 : [set: 'I_0] = set0 by apply/setP; case.
by rewrite /cpts e0 imset0 cards0.
Qed.

(** Textbook identity: every forest is a subset of the edge set ("a forest is a
    subgraph"). *)
Lemma forestb_sub (G:sgraph)(S:{set {set G}}) : forestb S -> S \subset edge2 G.
Proof. by rewrite /forestb => /andP[]. Qed.

(** [forestb] is satisfiable: the empty edge set on the empty graph is a forest. *)
Lemma forestb_set0_empty : forestb (G:=cycle_graph 0) set0.
Proof.
rewrite /forestb sub0set /= cards0 add0n cpts_I0.
by rewrite cardsT card_ord.
Qed.

(** ** Row 5 — [liftadj], [chiLift] *)

(** [liftadj] is irreflexive: the lift has no self-loops (it points strictly up). *)
Lemma liftadj_irrefl (h:nat)(p:{ffun ('I_5 * 'I_5) -> {perm 'I_h}})(a:'I_5 * 'I_h) :
  liftadj p a a = false.
Proof. by rewrite /liftadj ltnn. Qed.

(** ** Row 6 — [stable_solvableb], [Pstar] *)

(** [stable_solvableb] is satisfiable: on the empty population every profile is
    (vacuously) solvable. *)
Lemma stable_solvableb_I0 (pr:{ffun 'I_0 -> {perm 'I_0}}) : stable_solvableb pr.
Proof.
apply/existsP; exists [ffun x => x].
by apply/andP; split; apply/forallP; case.
Qed.

(** Textbook identity: the solvability probability is a nonnegative rational. *)
Lemma Pstar_ge0 (n:nat) : (0 <= Pstar n)%R.
Proof. by rewrite /Pstar; apply: divr_ge0; rewrite ler0z. Qed.

(** ** Row 7 — [radj], [three_connb], [polyhedralb], [cP], [Dk], [Bk] *)

(** Textbook identity: [three_connb] requires more than 3 vertices, so it is false
    on ['I_3]. *)
Lemma three_connb_I3 (E:{set {set 'I_3}}) : three_connb E = false.
Proof. by rewrite /three_connb card_ord ltnn. Qed.

(** Hence no graph on 3 vertices is "polyhedral", so [cP 3 k = 0]. *)
Lemma cP_3 (k:nat) : cP 3 k = 0.
Proof.
rewrite /cP; apply/eqP; rewrite cards_eq0; apply/eqP/setP=> E.
by rewrite !inE /polyhedralb three_connb_I3.
Qed.

(** Textbook identity: the empirical CDF count never exceeds the total count. *)
Lemma Bk_le_Dk (k:nat)(x:rat) : (Bk k x <= Dk k)%N.
Proof.
rewrite /Bk /Dk; apply: leq_sum => i _.
by case: ifP => _; [exact: leqnn | exact: leq0n].
Qed.
