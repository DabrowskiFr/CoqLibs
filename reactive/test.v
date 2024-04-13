
Definition addfix : forall (n m : nat), nat :=
    fix add (n m : nat) : nat := 
    match n with 
        | 0 => m 
        | S n => S (add n m)
    end.


Fixpoint add (n m : nat) : nat :=
    match n with 
        | 0 => m 
        | S n => S (add n m)
    end.

Print add.

(* fix, cofix : needs a product *)

Lemma add_rightneutral : forall n, add n 0 = n.
Proof.
    fix H 1.
    intro n.
    destruct n; simpl.
    - reflexivity.
    - rewrite H; reflexivity.
Qed.

CoInductive conat : Type :=
    | Z : conat 
    | N : conat -> conat.

CoFixpoint add' (n m : conat ) : conat :=
    match n with 
        | Z => m
        | N n => N (add' n m)
    end.

(* Pté coinductive sur inductive *)

Inductive P_coind_ind : conat -> Prop :=
    | P1 : P_coind_ind Z 
    | P2 : P_coind_ind (N Z).

CoInductive P_ind_coind : nat -> Prop := 
    Q1 : P_ind_coind 0.

Lemma c : forall (n : nat), P_ind_coind n.
Proof.
    fix H 1.
Admitted.

Lemma d : forall (n : nat), P_ind_coind n.
Proof.
    cofix H.
Admitted.

Lemma e : forall (n : conat), P_coind_ind n.
Proof.
    (* fix H 1. *)
    (* cofix H. *)
Admitted. 

(* redéfinition de l'égalité comme coinductif *)
(* mais plus grande propriété, est ce que cela correspond à l'égalité ?*)
CoInductive eq' {A : Type } : A -> A -> Prop :=
    eq'_ : forall n, eq' n n.

Lemma eq_eq' : forall (A : Type) (a b : A),
    eq a b -> eq' a b.
Proof.
    intros.
    subst.
    apply eq'_.
Qed.

Lemma eq'_eq : forall (A : Type) (a b : A),
    eq' a b -> eq a b.
Proof.
    intros.
    inversion H.
    reflexivity.
Qed.

Lemma u : forall A (a b c : A), eq' a b -> b = c -> a = c.
Proof.
    intros.
    inversion H.
    subst.
    reflexivity.
Qed.

Definition unroll (n : conat) : conat :=
    match n with Z => Z | N x => N x end.

Lemma unrollEq : forall n, n = unroll n.
Proof.
    destruct n; reflexivity.
Qed.

(* bisim -> equality *)

Lemma add'_rightneutral : forall n, add' n Z = n.
Proof.
    intro.
    apply eq'_eq.
    revert n.
    cofix H.
    intro n.
    destruct n.
    -   rewrite (unrollEq (add' Z Z)); simpl.
        apply eq'_.
    -   rewrite (unrollEq (add' (N n) Z)); simpl.
        generalize (H n); intro.
        apply eq'_eq in H0.
        apply eq_eq'.
        f_equal.
        apply H0.
Admitted.

