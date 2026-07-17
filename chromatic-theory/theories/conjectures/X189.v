(** * Chromatic.conjectures.X189 -- v2 spaghetti/path decomposition chi-bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X189 vocabulary ***********************************************)

Definition x189_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).

Definition x189_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x189_rooted_spaghetti_index
    (T : sgraph) (root : T) (bag : T -> {set T}) : Prop :=
  is_tree [set: T] /\
  forall v : T, connected [set t : T | v \in bag t].

Definition x189_spaghetti_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  exists root : T,
    is_tree [set: T] /\
    x189_tree_decomposition bag /\
    forall v : G, connected [set t : T | v \in bag t] /\
      (forall t : T, t \in [set u : T | v \in bag u] -> connect (--) root t).

Definition x189_spaghetti_path_decompositions_width (G : sgraph) (k : nat) : Prop :=
  exists (T P : sgraph) (tbag : T -> {set G}) (pbag : P -> {set G}),
    x189_spaghetti_tree_decomposition tbag /\
    x189_path_index_graph P /\
    x189_tree_decomposition pbag /\
    forall (t : T) (p : P), #|tbag t :&: pbag p| <= k.

(** ** X189 statements *****************************************************)

(** Conjecture 3: graphs admitting such a spaghetti/path decomposition pair are
    chi-bounded by a function of the intersection parameter [k]. *)
Definition spaghetti_tree_path_decomposition_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      x189_spaghetti_path_decompositions_width G k ->
      χ([set: G]) <= f k.
