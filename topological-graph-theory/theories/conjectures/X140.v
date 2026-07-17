(** * Topological.conjectures.X140 -- v2 random-embedding face-count row *)

From GTBase Require Export base.
From GraphTheory Require Import mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X140 vocabulary ***********************************************)

(** Maximum multiplicity of an unordered pair in a loopless multigraph. *)
Definition x140_edge_multiplicity (G : mgraph) (x y : G) : nat :=
  #|[set e : edge G | incident x e && incident y e]|.

Definition x140_max_edge_multiplicity_at_most
    (G : mgraph) (mu : nat) : Prop :=
  forall x y : G, x != y -> x140_edge_multiplicity x y <= mu.

Record x140_orientable_embedding (G : mgraph) := {
  x140_rotation_system : edge G -> bool;
  x140_faces : nat
}.

Definition x140_expected_random_embedding_faces_O
    (G : mgraph) (mu C : nat) : Prop :=
  exists (Emb : finType) (draw : Emb -> x140_orientable_embedding G),
    0 < #|{: Emb}| /\
    \sum_(e : Emb) x140_faces (draw e) <=
      C * (#|G| * (trunc_log 2 mu).+1) * #|{: Emb}|.

(** ** X140 statements *****************************************************)

(** Expected number of faces of random orientable embeddings is O(n log mu) for
    n-vertex loopless multigraphs of maximum edge multiplicity mu >= 2. *)
Definition expected_faces_random_orientable_embeddings_statement : Prop :=
  exists C N : nat,
    forall (n mu : nat) (G : mgraph),
      N <= n ->
      #|G| = n ->
      loopless G ->
      2 <= mu ->
      x140_max_edge_multiplicity_at_most G mu ->
      x140_expected_random_embedding_faces_O G mu C.
