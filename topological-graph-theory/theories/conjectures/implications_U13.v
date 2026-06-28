(** * Topological.conjectures.implications_U13 — milestone U13 edges

    Implication / refutation EDGES among the four U13 planar nodes
    (large induced forest; Earth–Moon; Wegner square-colouring; degenerate
    colouring), as Qed-closed RELATIVE theorems where one exists.

    OUTCOME (honest).  The four U13 rows are four MUTUALLY-INDEPENDENT famous
    open problems, grouped only by topic (planarity).  The verified-literature
    edge table of OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of them: there is
    no textbook "A ⟹ B" between any pair.  Consequently this milestone schedules
    ZERO verified edges — there is no real [Theorem A_implies_B. Qed] to add,
    because forcing one would either fail to compile or misstate the
    mathematics.  Per the edge policy a false/unclosing edge must NOT be forced.

    The single literature-MOTIVATED direction is recorded as a CANDIDATE
    annotation only (proved=false): the degenerate-colouring conjecture's k = 2
    clause makes the union of any two colour classes 1-degenerate, i.e. an
    induced forest (this is exactly an acyclic 5-colouring).  Taking the two
    largest of the five classes yields an induced forest on ≥ 2n/5 vertices
    (Albertson–Berman / Borodin), which is STRICTLY short of the n/2 (i.e.
    [#|G| <= 2*#|S|]) demanded by [large_induced_forest_in_a_planar_graph_statement].
    The constant gap 2/5 < 1/2 is real (five equal colour classes is a witness:
    every 2-class union has exactly 2n/5 vertices), so the implication does NOT
    close as a relative theorem and the edge stays a candidate, never scheduled.
    This is the same "looks-like-an-edge but the constant is wrong" pattern as
    the §6 withdrawn edges (list-total ⟹ Behzad, list-Hadwiger ⟹ Hadwiger).

    The file is self-contained (it re-states the four U13 nodes verbatim so the
    edge endpoints are in scope) and axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** U13 nodes (verbatim from Topological.conjectures.U13) *)

Definition large_induced_forest_in_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.

Definition union_of_two_planar
    (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ is_planar (SGraph s1 i1),
        is_planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].

Definition earth_moon_statement : Prop :=
  forall (is_planar : sgraph -> Prop),
    (exists G0 : sgraph, union_of_two_planar is_planar G0) ->
    exists m : nat,
      (forall G : sgraph, union_of_two_planar is_planar G -> (χ([set: G]) <= m)%N)
   /\ (exists G : sgraph, union_of_two_planar is_planar G /\ χ([set: G]) = m).

Definition colouring_the_square_of_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G -> (0 < #|G|)%N ->
    [/\ ( Delta G = 3 -> (χ([set: graph_power G 2]) <= 7)%N ),
        ( (4 <= Delta G)%N -> (Delta G <= 7)%N ->
            (χ([set: graph_power G 2]) <= Delta G + 5)%N )
      & ( (8 <= Delta G)%N ->
            (χ([set: graph_power G 2]) <= (3 * Delta G)./2 + 1)%N ) ].

Definition k_degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G},
    S \subset W -> S != set0 ->
    exists x : G, x \in S /\ (#|N(x) :&: S| <= k)%N.

Definition k_degenerate (G : sgraph) (k : nat) : Prop :=
  k_degenerate_on [set: G] k.
Arguments k_degenerate_on {G} W k.

Definition degenerate_colorings_of_planar_graphs_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists col : G -> 'I_5,
      (forall x y : G, x -- y -> col x != col y)
   /\ (forall T : {set 'I_5},
         (1 <= #|T|)%N -> (#|T| <= 4)%N ->
         k_degenerate_on [set v : G | col v \in T] (#|T| - 1)).

(** ** Edges

    No verified-literature edge exists among the four nodes (plan §6 lists
    none).  The only literature-motivated direction is a CANDIDATE blocked by a
    constant gap, recorded as an annotation only — there is no Qed theorem for
    it because it does not logically close. *)

(*@EDGE from=degenerate_colorings_of_planar_graphs_statement to=large_induced_forest_in_a_planar_graph_statement kind=implies status=candidate proved=false cite="Albertson & Berman 1979 (induced-forest conj.); Borodin 1979 (acyclic 5-colouring of planar graphs)" note="k=2 clause: union of any two of the five colour classes is 1-degenerate, i.e. an induced forest (acyclic colouring). Largest 2-class union has only >= 2n/5 vertices, strictly short of the n/2 (#|G| <= 2*#|S|) required by the target. Five equal classes is a witness that 2/5 cannot be improved by this argument, so the edge does NOT close; candidate, never scheduled." *)
