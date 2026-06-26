(** * Digraph.main — ACₙ[ACₙ] is 5-ω̄-critical: Conjecture 5.10 at k = 5

    Assembly of the k = 5 theorem (paper §3–§6). For every odd n = 2m+1
    with m ≥ 3, the tournament T = ACₙ[ACₙ]:
    - has ω̄(T) = 5                     ([omegabar_T5]: k5_lower + k5_upper);
    - has ω̄(T − v) = 4 for EVERY v     ([omegabar_T5_del]: the bound at
      (0,0) spreads to all vertices by vertex-transitivity of the product);
    - is hence 5-ω̄-critical            ([T5_kcritical5]);
    - has order n²                      ([card_T5]),

    so distinct n give an infinite family of 5-ω̄-critical tournaments —
    Conjecture 5.10 of Aboulker–Aubian–Charbit–Lopes at k = 5
    ([conjecture_5_10_at_k5]). Moreover every proper subtournament has
    ω̄ ≤ 4 ([proper_sub_omegabar_le4]), so the only subtournament with
    ω̄ ≥ 5 is T itself, of unbounded order: no bound ℓ(5) exists and
    Question 5.9 fails at k = 5 ([question_5_9_fails_at_k5]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base k5_lower.
From Digraph Require Import in_neighbourhood cells obstructions coverage k5_upper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Main.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation T5 := (lexprod_tournament ACm ACm).

Let z0 : ACm := (0 : 'Z_n).
Let o00 : T5 := (z0, z0).

(** The product of the vertex-transitive ACₙ with itself is
    vertex-transitive. *)
Lemma T5_vertex_transitive : vertex_transitiveb (T5 : diGraphType).
Proof.
exact: (lexprod_vertex_transitive
          (AC_vertex_transitive m') (AC_vertex_transitive m')).
Qed.

(** ** ω̄(T) = 5 *)

Theorem omegabar_T5 : ω̄(T5) = 5.
Proof.
apply/anti_leq/andP; split; first exact: omegabar_T_le5.
exact: (omegabar_T_ge5 m3).
Qed.

(** ** ω̄(T − v) = 4 for every vertex v *)

Theorem omegabar_T5_del (v : T5) : ω̄(del_tournament v) = 4.
Proof.
rewrite (omegabar_del_vt T5_vertex_transitive v o00).
apply/anti_leq/andP; split; first exact: omegabar_Tdel_le4.
exact: (omegabar_Tdel_ge4 m3).
Qed.

(** ** T is 5-ω̄-critical *)

Theorem T5_kcritical5 : kcritical 5 T5.
Proof.
rewrite (vt_kcritical 5 o00 T5_vertex_transitive).
by rewrite omegabar_T5 omegabar_T5_del !eqxx.
Qed.

(** ** T has order n² *)

Lemma card_T5 : #|T5| = (n * n)%N.
Proof. by rewrite card_lexprod !card_AC. Qed.

(** ** Every proper subtournament has ω̄ ≤ 4 *)

Theorem proper_sub_omegabar_le4 (S : {set T5}) :
  S != [set: T5] -> (ω̄(sub_tournament S) <= 4)%N.
Proof.
move=> Sproper.
have /subsetPn[v _ vNS] : ~~ ([set: T5] \subset S).
  by move: Sproper; apply: contraNN => sub; rewrite eqEsubset sub subsetT.
have memf (x : sub_tournament S) : val x \in [set~ v].
  by rewrite !inE; apply: contraNneq vNS => <-; exact: (valP x).
pose f (x : sub_tournament S) : del_tournament v := Sub (val x) (memf x).
have f_inj : injective f.
  by move=> x y /(congr1 val); rewrite !SubK => /val_inj.
have f_arc (x y : sub_tournament S) : (f x --> f y) = (x --> y).
  by rewrite !sub_arcE !SubK.
apply: leq_trans (omegabar_embed f_inj f_arc) _.
by rewrite omegabar_T5_del.
Qed.

End Main.

(** ** Conjecture 5.10 at k = 5: an infinite family

    For every N there is a 5-ω̄-critical tournament on more than N
    vertices. *)

Theorem conjecture_5_10_at_k5 (N : nat) :
  exists T : tournament, kcritical 5 T /\ (N < #|T|)%N.
Proof.
pose k := maxn 2 N.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
exists (lexprod_tournament (AC k) (AC k)); split.
  exact: (T5_kcritical5 m3).
rewrite card_T5.
have kn : (k < (k.+1).*2.+1)%N.
  by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
exact: leq_ltn_trans (leq_maxr 2 N) (leq_trans kn (leq_pmulr _ _)).
Qed.

(** ** Question 5.9 fails at k = 5

    No bound ℓ(5) exists: for every L there is a 5-ω̄-critical tournament
    on more than L vertices whose ONLY subtournament with ω̄ ≥ 5 is the
    whole tournament. *)

Theorem question_5_9_fails_at_k5 (L : nat) :
  exists T : tournament,
    [/\ kcritical 5 T, (L < #|T|)%N
      & forall S : {set T}, (5 <= ω̄(sub_tournament S))%N -> S = [set: T]].
Proof.
pose k := maxn 2 L.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
exists (lexprod_tournament (AC k) (AC k)); split.
- exact: (T5_kcritical5 m3).
- rewrite card_T5.
  have kn : (k < (k.+1).*2.+1)%N.
    by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
  exact: leq_ltn_trans (leq_maxr 2 L) (leq_trans kn (leq_pmulr _ _)).
- move=> S h5; case: (eqVneq S [set: _]) => // neq.
  by have := leq_trans h5 (proper_sub_omegabar_le4 m3 neq).
Qed.
