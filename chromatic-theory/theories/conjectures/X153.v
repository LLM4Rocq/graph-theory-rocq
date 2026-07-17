(** * Chromatic.conjectures.X153 -- v2 planar girth-5 list-critical subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X153 vocabulary ***********************************************)

Definition x153_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition x153_short_cycle (G : sgraph) (k : nat) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\ size c <= k.

Definition x153_cycle_precoloured_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G) : Prop :=
  forall v : G,
    if v \in x153_cycle_vertices c1 :|: x153_cycle_vertices c2
    then #|L v| = 1
    else 3 <= #|L v|.

Definition x153_list_colourable_induced
    (G : sgraph) (C : finType) (L : G -> {set C}) (S : {set G}) : Prop :=
  @list_colourable (induced S) C (fun v : induced S => L (val v)).

(** ** X153 statements *****************************************************)

(** Conjecture 1.7 (arXiv:1302.2158): for each cycle-length bound [k] there is
    a bounded-size subgraph witnessing non-list-colourability when a planar
    girth-at-least-five graph with two precoloured short cycles is not
    list-colourable.  The source says "subgraph"; using the induced subgraph on
    the same vertex set is equivalent for non-colourability, since adding edges
    cannot create a colouring. *)
Definition planar_girth5_two_cycles_list_critical_subgraph_statement : Prop :=
  forall k : nat,
    5 <= k ->
    exists K : nat,
      forall (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G),
        wagner_planar G ->
        girth_geq G 5 ->
        x153_short_cycle k c1 ->
        x153_short_cycle k c2 ->
        x153_cycle_precoloured_lists L c1 c2 ->
        ~ @list_colourable G C L ->
        exists S : {set G},
          [/\ #|S| <= K,
              x153_cycle_vertices c1 \subset S,
              x153_cycle_vertices c2 \subset S &
              ~ x153_list_colourable_induced L S].

