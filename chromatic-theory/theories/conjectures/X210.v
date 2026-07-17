(** * Chromatic.conjectures.X210 -- v2 surface conflict-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X210 vocabulary ***********************************************)

Definition x210_euler_genus_embeddable (G : sgraph) (g : nat) : Prop :=
  surface_embeddable g G.

Definition x210_conflict_assignment
    (G : sgraph) (k C : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_k, F u v a b = F v u b a) /\
  (forall u v : G, u -- v ->
    #|[set ab : 'I_k * 'I_k | F u v ab.1 ab.2]| <= C * k).

Definition x210_conflict_colouring
    (G : sgraph) (k : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  exists col : G -> 'I_k,
    forall u v : G, u -- v -> ~~ F u v (col u) (col v).

Definition x210_conflict_k_colourable_under_bound
    (G : sgraph) (k C : nat) : Prop :=
  forall F : G -> G -> 'I_k -> 'I_k -> bool,
    @x210_conflict_assignment G k C F -> @x210_conflict_colouring G k F.

(** ** X210 statements *****************************************************)

(** Dvorak-Esperet-Kang-Ozeki Conjecture 3: surface-embeddable graphs should be
    conflict [k]-colourable under a linear-in-[k] conflict bound when
    [k >= C' sqrt(g)]. *)
Definition surface_conflict_colouring_sqrt_genus_statement : Prop :=
  exists C C' : nat,
    forall (G : sgraph) (g k : nat),
      x210_euler_genus_embeddable G g ->
      C' * g <= k * k ->
      x210_conflict_k_colourable_under_bound G k C.
