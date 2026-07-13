(** * Extremal.conjectures.X118 -- v2 Conlon-Fox-Sudakov dense pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X118 vocabulary ***********************************************)

(** Erdos--Hajnal convention: [H]-free means [G] has no *induced* copy of [H]. *)
Definition x118_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** Number of edges between disjoint sets [A] and [B]: the ordered pairs
    [(a, b)] with [a \in A], [b \in B] and [a -- b].  As [A] and [B] are
    disjoint each cross edge is counted exactly once, and the total number of
    ordered pairs is [#|A| * #|B|]; so the edge-density between [A] and [B] is
    [x118_edges_between A B / (#|A| * #|B|)]. *)
Definition x118_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** ** X118 statements *****************************************************)

(** Conlon--Fox--Sudakov, dense pair (an Erdos--Hajnal density variant): for
    every graph [H] there exist [eps, sigma > 0] such that for every [H]-free
    graph [G] on [n > 1] vertices and all [c] with [0 <= c <= 1/2], [V(G)]
    contains disjoint [A, B] with [#|A| >= eps * c^sigma * n] and
    [#|B| >= eps * n] whose edge-density is [<= c] or [>= 1 - c].

    Rationals: [eps = e1/e2], [sigma = s1/s2] (all four numbers positive),
    [c = c1/c2] with [0 <= c1] and [c <= 1/2] encoded as [2*c1 <= c2].  The
    fractional-power size bounds are cleared by raising to the power [s2] and
    cross-multiplying (so [c^sigma = c^{s1/s2}] becomes [c1^s1 / c2^s1]):
      [#|A| >= eps*c^sigma*n]  <->  [e1^s2 * c1^s1 * n^s2 <= e2^s2 * c2^s1 * #|A|^s2],
      [#|B| >= eps*n]          <->  [e1 * n <= e2 * #|B|].
    Density [<= c] is [c2 * e(A,B) <= c1 * #|A| * #|B|]; density [>= 1 - c] is
    [(c2 - c1) * #|A| * #|B| <= c2 * e(A,B)]. *)
Definition conlon_fox_sudakov_dense_pair_statement : Prop :=
  forall H : sgraph,
    exists e1 e2 s1 s2 : nat,
      [/\ 0 < e1, 0 < e2, 0 < s1 & 0 < s2] /\
      forall G : sgraph,
        1 < #|G| ->
        x118_induced_free G H ->
        forall c1 c2 : nat,
          0 < c2 -> 2 * c1 <= c2 ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                e1 ^ s2 * c1 ^ s1 * #|G| ^ s2 <= e2 ^ s2 * c2 ^ s1 * #|A| ^ s2,
                e1 * #|G| <= e2 * #|B|
              & (c2 * x118_edges_between A B <= c1 * (#|A| * #|B|) \/
                 (c2 - c1) * (#|A| * #|B|) <= c2 * x118_edges_between A B)].
