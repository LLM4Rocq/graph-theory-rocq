(** * Chromatic.foundations.chi_bounding -- polynomial chi-bounding wrappers (WP4b)

    The chi-boundedness rows of waves X213 and X218 all measure a class of finite
    simple graphs by ONE bounding function of the clique number.  Two wrappers are
    shared here instead of being re-encoded in each conjecture file:

      [chi_bounded_class F]  -- some [f : nat -> nat] bounds chi by f(omega) on F;
      [poly_chi_bounded F]   -- some [c], [d] bound chi by c * omega^d on F,
                                the "polynomially chi-bounded" of the sources.

    Both quantify the bounding data BEFORE the graphs of the class, which is the
    intended reading of "the class is (polynomially) chi-bounded"; a per-graph
    choice would be vacuous.  Neither notion exists in coq-graph-theory or in
    GTBase; [U8.v] owns a [chi_bounded] with the same meaning as
    [chi_bounded_class] (see the note below) and is kept as the citable name of
    the Gyarfas-Sumner row. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A class [F] of graphs is chi-bounded: one function of the clique number
    bounds the chromatic number over the whole class.  (Definitionally the same
    shape as [U8.chi_bounded]; that name stays the citable one of the
    Gyarfas-Sumner corpus row, this one is the reusable wrapper.) *)
Definition chi_bounded_class (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** A class [F] is POLYNOMIALLY chi-bounded: the bounding function may be taken
    of the form [t |-> c * t ^ d].  Over the naturals this is exactly "bounded by
    a polynomial in omega", since every polynomial with natural coefficients of
    degree [d] is dominated by (sum of coefficients) * t^d for t >= 1, and the
    t = 0 case is covered because [0 ^ 0 = 1]. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Sanity lemmas ******************************************************)

(** Non-vacuity: the class of graphs with at most one vertex is polynomially
    chi-bounded ([c = 1], [d = 0]); the witness is concrete, not the empty class. *)
Lemma poly_chi_bounded_small : poly_chi_bounded (fun G : sgraph => #|G| <= 1).
Proof.
exists 1, 0 => G le1; rewrite expn0 muln1.
by apply: leq_trans (leq_chi _) _; rewrite cardsT.
Qed.

(** Structural law: a polynomial bound is a bound. *)
Lemma poly_chi_boundedW (F : sgraph -> Prop) :
  poly_chi_bounded F -> chi_bounded_class F.
Proof. by case=> c [d] H; exists (fun t => c * t ^ d). Qed.

(** Both notions are hereditary along class inclusion. *)
Lemma poly_chi_bounded_sub (F F' : sgraph -> Prop) :
  (forall G, F G -> F' G) -> poly_chi_bounded F' -> poly_chi_bounded F.
Proof. by move=> sub [c [d H]]; exists c, d => G FG; apply: H; apply: sub. Qed.

(** Arithmetic helper: a base of at most one stays at most one under powers
    (the [d = 0] corner uses [0 ^ 0 = 1]). *)
Lemma expn_leq1 (m d : nat) : m <= 1 -> m ^ d <= 1.
Proof.
rewrite leq_eqVlt ltnS leqn0 => /orP[/eqP->|/eqP->]; first by rewrite exp1n.
by case: d => [|d']; rewrite ?expn0 // exp0n.
Qed.

(** Guard has teeth: a class on which the chromatic number is unbounded while
    the clique number stays at most one is NOT polynomially chi-bounded, so the
    wrapper really constrains the class (it is not satisfied by every class). *)
Lemma not_poly_chi_bounded_of_unbounded (F : sgraph -> Prop) :
  (forall n : nat, exists G : sgraph,
      [/\ F G, ω([set: G]) <= 1 & n < χ([set: G])]) ->
  ~ poly_chi_bounded F.
Proof.
move=> unb [c [d H]]; have [G [FG wle clt]] := unb c.
have wle1 := expn_leq1 d wle.
have : χ([set: G]) <= c.
  by apply: leq_trans (H G FG) _; rewrite -{2}(muln1 c) leq_mul2l wle1 orbT.
by rewrite leqNgt clt.
Qed.

Print Assumptions poly_chi_bounded_small.
Print Assumptions poly_chi_boundedW.
Print Assumptions not_poly_chi_bounded_of_unbounded.
