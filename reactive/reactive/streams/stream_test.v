(** printing ∼ #&sim;# *)
(** printing ∘ #&#8728; # *)
(** printing ⋅ #&middot; # *)

From reactive.streams Require Import stream.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Category.
From reactive.utils Require Import Functor.
From reactive.streams Require Import streamFunctor.

Open Scope stream_scope.

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

(* L'utilisation doit être guardée par un constructeur *)
(* il n'y a pas de constructeur pour faire grossir le terme *)
(* d'ou le besoin de bisimilar, pas de cas inductif pour eq *)
Lemma ax : forall {A : Type} (s1 s2 : stream A),
    eq_str s1 s2 -> eq' s1 s2.
Proof.
    intros A.
    cofix H.
    intros.
    inversion H0; subst.
    destruct s1, s2; simpl in *.
    apply eq_eq'.
    f_equal.
    assumption.
    apply eq'_eq.
    apply H.
    apply H2.
    Admitted.
    
(** *** Examples *)
(** Example 1: *)
(** We prove that a === true b where a = true false a and b = false true b *)

CoFixpoint a : stream bool := true ⋅ false ⋅ a.

CoFixpoint b : stream bool := false ⋅ true ⋅ b.

Inductive R : stream bool -> stream bool -> Prop :=
    | Ra : R a (true ⋅ b)
    | Rb : R (false ⋅ a) b.

Fact eq_str_closed_R : eq_str_closed R.
Proof.
    constructor.
    -   intros s1 s2 H.
        destruct H; reflexivity.
    -   intros s1 s2 H.
        destruct H.
        +   exact Rb.
        +   exact Ra.
Qed.

Lemma example1 : a ∼ true ⋅ b.
Proof.
    exact (eq_str_gfp eq_str_closed_R _ _ Ra).
Qed.

(** Example 2 *)
(** We prove that ones === oneones *)

CoFixpoint ones : stream nat := 1 ⋅ ones.

CoFixpoint oneones : stream nat := 1 ⋅ 1 ⋅ oneones.

Inductive R2 : stream nat -> stream nat -> Prop :=
    | R2a : R2 ones oneones
    | R2b : R2 ones (1 ⋅ oneones).

Fact eq_str_closed_R2 : eq_str_closed R2.
Proof.
    constructor; intros _ _ [ | ]; auto using R2.
Qed.

Lemma example2 : ones ∼ oneones.
Proof.
    exact (eq_str_gfp eq_str_closed_R2 _ _ R2a).
Qed.

(** Example 3 *)
(** We prove that ones = map f (tl s) *)

CoFixpoint map {A B : Type} (f : A -> B) (s : stream A) : stream B :=
    (f (hd s)) ⋅ (map f (tl s)).

Inductive R3 : stream nat -> stream nat -> Prop :=
    | R3a : R3 (map id ones) ones.

Fact eq_str_closed_R3 : eq_str_closed R3.
Proof.
    constructor; intros s1 s2 [ ]; auto using R3.
Qed.

Lemma example3 : map id ones ∼ ones.
Proof.
    exact (eq_str_gfp eq_str_closed_R3 _ _ R3a).
Qed.

(* Equivalence de fonction : f ~ g ssi forall s, f s === g s *)

(** Examples 4 et 5 *)
(** On montre que (stream, map) est un foncteur pour la relation 
    d'équivalence ~ définie par f ~ g ssi forall s, f s === g s *)
(** - forall s, map id ~ id *)
(** - forall s, map (g ∘ f) ~ (map f ∘ map g) *)

Inductive R4 (A : Set) : stream A -> stream A -> Prop :=
    R4a : forall s, R4 A (map id s) s.

Lemma eq_str_closed_R4 : forall (A : Set), eq_str_closed (R4 A).
Proof.
    constructor.
    -   intros s1 s2 []; auto.
    -   intros s1 s2 H.
        inversion H; subst.
        simpl.
        exact (R4a A (tl s2)).
Qed.


Lemma example4 : forall {A : Set} (s : stream A), 
    (map id s) ∼ id s.
Proof.
    intros A s.
    exact (eq_str_gfp (eq_str_closed_R4 A) _ _ (R4a A s)).
Qed.


(* CoFixpoint map_stream {A B : Type} (f : A -> B) : stream A -> stream B :=
    fun s => match s with 
        str a s => str (f a) (map_stream f s)
    end. *)

    Inductive R5 (C : Set) : stream C -> stream C -> Prop :=
    R5a : forall (A B : Set) (s : stream A) (f : A -> B) (g : B -> C),
    R5 C ((fmap g ∘ fmap f) s) 
        (fmap (@compose _ Type_Category _ _ _ g  f) s).

(* Inductive R5 (C : Set) : stream C -> stream C -> Prop :=
    R5a : forall (A B : Set) (s : stream A) (f : A -> B) (g : B -> C),
    R5 C ((fmap g ∘ fmap f) s) 
        (fmap (@compose _ Type_Category _ _ _ g  f) s). *)

Fact eq_str_closed_R5 : forall (C : Set), eq_str_closed (R5 C).
Proof.
    constructor.
    -   intros s1 s2 H.
        destruct H.
        destruct s.
        reflexivity.
    -   intros s1 s2 [].
        simpl.
        destruct s.
        apply R5a.
Qed.

(* Lemma example5 : forall (A B C : Set) (f : A -> B) (g : B -> C) (s : stream A),
    (map g ∘ map f) s ∼ map (g ∘ f) s.
Proof.
    intros.
    apply (eq_str_gfp (eq_str_closed_R5 C)). 
    apply R5a.
Qed. *)

