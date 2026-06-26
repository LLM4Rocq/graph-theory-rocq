(** * Digraph.circulant — circulant digraphs over 'Z_n and the tournament ACₙ

    'Z_n's canonical [finGroupType] is the *additive* group ([1%g] is [0],
    [*%g] is [+], [_^-1] is [-_] — definitionally, see the bridge lemmas), so
    circulant digraphs are literally Cayley digraphs over ['Z_n]:
    [x --> y iff y - x ∈ A].

    The flagship instance is the paper's tournament [AC m] on
    [n = 2m+1] vertices, with connection set

      [ACset = {1, …, m−1} ∪ {m+1} ⊆ 'Z_n]

    ([arXiv:2310.04265]; docs/DESIGN.md §7). [ACset_cond] is the residue
    argument that [ACset] hits each pair [{z, −z}] (z ≠ 0) exactly once —
    hence [AC m] is a tournament (M2 exit) — and as a Cayley digraph it is
    vertex-transitive. To keep every instance hypothesis-free, the parameter
    is [m'] with [m := m'.+1] (so m ≥ 1, n = 2m+1 ≥ 3; [AC 0] is the reversed
    triangle). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude digraph oriented tournament automorphism cayley.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** 'Z_p group operations are the additive ones — definitionally *)

Section ZpGroupBridge.
Variable p : nat.

Lemma Zp_mulgE (x y : 'Z_p) : (x * y)%g = x + y.
Proof. by []. Qed.

Lemma Zp_invgE (x : 'Z_p) : (x^-1)%g = - x.
Proof. by []. Qed.

Lemma Zp_1gE : (1%g : 'Z_p) = 0.
Proof. by []. Qed.

Lemma val_Zp_opp (z : 'Z_p) : val (- z) = ((p.-2.+2 - val z) %% p.-2.+2)%N.
Proof. by []. Qed.

(** Circulant arc characterization: [x --> y] iff the difference is a
    connection element. *)
Lemma circulant_arcE (A : {set 'Z_p}) (x y : cayley A) :
  (x --> y) = (y - x \in A).
Proof. by rewrite cayley_arcE Zp_mulgE Zp_invgE addrC. Qed.

End ZpGroupBridge.

(** ** The tournament ACₙ, n = 2m+1 *)

Section AC.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).

Definition ACset : {set 'Z_n} :=
  [set z : 'Z_n | ((0 < val z < m) || (val z == m.+1))%N].

(** [val] of the opposite, with the truncation resolved (n ≥ 3). *)
Let val_oppE (z : 'Z_n) : val (- z) = ((n - val z) %% n)%N.
Proof. by []. Qed.

(** The connection set hits each pair {z, −z} (z ≠ 0) exactly once — this is
    the residue-arithmetic heart of "ACₙ is a tournament". *)
Lemma ACset_cond (z : 'Z_n) : (z != 0) = (z \in ACset) (+) (- z \in ACset).
Proof.
case: (eqVneq z 0) => [->|zN0] /=.
- by rewrite oppr0 addbb.
- have vpos : (0 < val z)%N.
    by rewrite lt0n -[0%N]/(val (0 : 'Z_n)) val_eqE.
  have vlt : (val z < n)%N := ltn_ord z.
  rewrite !inE val_oppE modn_small ?ltn_subrL ?vpos //.
  case: (ltngtP (val z) m) => [vltm|mltv|veqm].
  - (* 0 < v < m : z ∈ ACset, and n−v ≥ m+2 keeps −z out *)
    have wgt : (m.+1 < n - val z)%N.
      move: (val z) vltm => v hv.
      by rewrite ltn_subRL -addnn addnS ltnS addnC ltn_add2l ?(ltnW hv).
    by rewrite (gtn_eqF wgt) (leq_gtF (ltnW (ltn_trans (ltnSn m) wgt))) andbF.
  - (* m < v *)
    case: (ltngtP (val z) m.+1) => [vlt1|vgt1|veq1].
    + by move: vlt1; rewrite ltnS leqNgt mltv.
    + (* v ≥ m+2 : −z ∈ ACset via 0 < n−v < m *)
      have w_pos : (0 < n - val z)%N by rewrite subn_gt0.
      have wltm : (n - val z < m)%N.
        rewrite ltn_subLR ?(ltnW vlt) //.
        move: (val z) vgt1 => v hv.
        apply: (@leq_trans (m.+2 + m)%N); last by rewrite leq_add2r.
        by rewrite -addnn !addSn !ltnS.
      by rewrite w_pos wltm.
    + (* v = m+1 : z ∈ ACset, n−v = m ∉ ACset *)
      rewrite veq1.
      have -> : (n - m.+1)%N = m by rewrite -addnn subSS addnK.
      by rewrite ltnn andbF (ltn_eqF (ltnSn m)).
  - (* v = m : z ∉ ACset, n−v = m+1 ∈ ACset *)
    rewrite veqm (ltn_eqF (ltnSn m)).
    have -> : (n - m)%N = m.+1 by rewrite -addnn -addSn addnK.
    by rewrite (leq_gtF (leqnSn m)) andbF eqxx.
Qed.

(** ACₙ is a tournament. *)

Fact AC_irrefl : irreflexive (arc : rel (cayley ACset)).
Proof.
have h1 : 1%g \notin ACset by rewrite inE.
by case: (@cayley_irreflP _ ACset) => _ /(_ h1).
Qed.

Fact AC_total (x y : cayley ACset) : (x != y) = (arc x y) (+) (arc y x).
Proof.
case: (@cayley_totalP _ ACset) => _ h; apply: h => z.
by rewrite Zp_1gE Zp_invgE ACset_cond.
Qed.

HB.instance Definition _ :=
  DiGraph_IsTournament.Build (cayley ACset) AC_irrefl AC_total.

Definition AC : tournament := cayley ACset : tournament.

Lemma AC_arcE (x y : AC) : (x --> y) = (y - x \in ACset).
Proof. exact: circulant_arcE. Qed.

Lemma card_AC : #|AC| = n.
Proof. exact: card_ord. Qed.

(** ACₙ is vertex-transitive (as any Cayley digraph: translations act
    transitively) — the M2 exit fact feeding the M3 criticality reduction. *)
Lemma AC_vertex_transitive : vertex_transitiveb AC.
Proof. exact: cayley_vertex_transitive. Qed.

End AC.

(** ** C₃ is vertex-transitive

    [C3]'s arc relation [v == u + 1] over 'Z_3 is translation-invariant,
    so the translations x ↦ x + t are automorphisms and act transitively
    (the Cayley-translation argument in miniature; G3 of
    docs/k34_dossier.md — feeds the k = 4 criticality reduction). *)

Lemma C3_vertex_transitive : vertex_transitiveb (C3 : diGraphType).
Proof.
apply/vertex_transitivebP=> u v.
have tinj : injective (fun x : C3 => (((x : 'Z_3) + (v - u) : 'Z_3) : C3)).
  exact: addIr.
exists (perm tinj); last by rewrite permE /= addrC subrK.
rewrite dgautE; apply/autbP=> x y; rewrite !permE !arcC3E /=.
by rewrite addrAC (inj_eq (addIr _)).
Qed.
