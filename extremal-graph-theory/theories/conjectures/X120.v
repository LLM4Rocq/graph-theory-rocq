(** * Extremal.conjectures.X120 -- v2 Conlon-Fox-Sudakov sparse pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X120 vocabulary ***********************************************)

(** Erdos--Hajnal convention: [H]-free means no *induced* copy of [H].
    (Kept local so this file is self-contained and does not import X118.) *)
Definition x120_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** Cross edges between disjoint [A] and [B] in [G]: ordered pairs [(a, b)]
    with [a \in A], [b \in B], [a -- b] (each counted once as [A], [B] are
    disjoint). *)
Definition x120_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** Cross edges between [A] and [B] in the complement [G-bar]: ordered pairs
    [(a, b)], [a \in A], [b \in B], with [a] and [b] *non*-adjacent in [G].
    As [A], [B] are disjoint we have [a <> b], so these are exactly the edges
    of [G-bar] between [A] and [B] (equal to [#|A|*#|B| - e_G(A,B)]). *)
Definition x120_nonedges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & ~~ (p.1 -- p.2)]]|.

(** ** X120 statements *****************************************************)

(** Conlon--Fox--Sudakov, sparse pair: for every graph [H] there exist
    [c1, c2 > 0] such that for every [H]-free graph [G] with [#|G| >= 2] and
    all [x] in [(0, 1/2)], there exist disjoint [A, B \subseteq V(G)] with
    [#|A|, #|B| >= x^{c1} * #|G|^{c2}] such that [B] is [x]-sparse to [A] in
    one of [G], [G-bar].

    "[B] is [x]-sparse to [A]" means the edge-density between [A] and [B] is
    [<= x], i.e. [e(A,B) <= x * #|A| * #|B|]; "in one of [G], [G-bar]" is the
    disjunction over [G] and its complement.  Rationals: [x = xn/xd] with
    [0 < x < 1/2] encoded as [0 < xn] and [2*xn < xd]; exponents [c1 = a1/a2],
    [c2 = b1/b2] with all four numbers positive, chosen (per [H]) before [G].
    The fractional-power size bounds are cleared by raising to the power
    [a2*b2] and cross-multiplying:
      [#|A| >= x^{c1} * #|G|^{c2}]  <->
        [xn^(a1*b2) * #|G|^(b1*a2) <= xd^(a1*b2) * #|A|^(a2*b2)].
    [x]-sparse in [G] is [xd * e_G(A,B) <= xn * #|A| * #|B|]; in [G-bar] it is
    [xd * e_{G-bar}(A,B) <= xn * #|A| * #|B|]. *)
Definition conlon_fox_sudakov_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists a1 a2 b1 b2 : nat,
      [/\ 0 < a1, 0 < a2, 0 < b1 & 0 < b2] /\
      forall G : sgraph,
        2 <= #|G| ->
        x120_induced_free G H ->
        forall xn xd : nat,
          0 < xn -> 2 * xn < xd ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|A| ^ (a2 * b2),
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|B| ^ (a2 * b2)
              & (xd * x120_edges_between A B <= xn * (#|A| * #|B|) \/
                 xd * x120_nonedges_between A B <= xn * (#|A| * #|B|))].
