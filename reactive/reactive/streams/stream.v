
From Coq.Setoids Require Import Setoid.
From Coq.Logic Require Import FunctionalExtensionality.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Category.
From reactive.utils Require Import Functor.
From reactive.utils Require Import Algebra.

Declare Scope stream_scope.
Open Scope type_scope.
(** * Streams *)
(** Streams for a coalgebra *)

Section Stream.

    CoInductive stream (A : Type) : Type := 
        str : A -> stream A -> stream A.

    Global Arguments str {A}.
    
    Definition Fₛ (A : Type) (X : Type) := A * X.

    #[refine] Instance functor_f (A : Type) : Functor (Fₛ A) := 
        { fmap := fun _ _ f p => (fst p, f (snd p)) }.
    Proof.
        -   intros U [a u]; reflexivity.
        -   intros U V W g h [a u]; reflexivity.
    Qed.

    Instance stream_CoAlgebra ( A : Type ) : CoAlgebra (Fₛ A) (stream A) := 
        { out := fun s => match s with str a s => (a,s) end }.

    Definition hd { A : Type }: stream A -> A := fst ∘ out.

    Definition tl { A : Type }: stream A -> stream A := snd ∘ out.

    Fixpoint nth_stream {A : Type} (s : stream A) (n : nat) : A :=
        match n with 0 => hd s | S n => nth_stream (tl s) n end.

End Stream.

Infix "⋅" := str (at level 60, right associativity) : stream_scope. 

(** ** Equivalence *)
(** we define a equivalence relation over streams as
the largest bisimulation. It is equivalent to
equality of elements *)

Section Equiv.

    Context {A : Type}.

    CoInductive eq_str : stream A -> stream A -> Prop :=
        eq_str_str : forall s₁ s₂,
            hd s₁ = hd s₂ -> 
            eq_str (tl s₁) (tl s₂) -> eq_str s₁ s₂.

    Infix "∼" := eq_str (at level 60, right associativity).

    Record eq_str_closed (R : relation (stream A)) : Prop :=
        {
            eq_str_hd : forall s₁ s₂, R s₁ s₂ -> hd s₁ = hd s₂;
            eq_str_tl : forall s₁ s₂, R s₁ s₂ -> R (tl s₁) (tl s₂)
        }.
    
    Context {R : relation (stream A)} (RBisim : eq_str_closed R).
    
    Theorem eq_str_gfp : forall s₁ s₂, R s₁ s₂ -> s₁ ∼ s₂.
    Proof.
        cofix HInd.
        intros s1 s2 H_R.
        constructor.
        -   exact (eq_str_hd R RBisim s1 s2 H_R).
        -   assert (R (tl s1) (tl s2)) as H_Rtl by
                exact (eq_str_tl R RBisim s1 s2 H_R).
            exact (HInd (tl s1) (tl s2) H_Rtl).
    Qed.

    Lemma eq_str_refl : forall (s : stream A), s ∼ s.
    Proof.
        cofix HInd.
        intros [a s].
        constructor; [reflexivity | exact (HInd s)].
    Qed.

    Lemma eq_str_sym : forall (s₁ s₂ : stream A), s₁ ∼ s₂ -> s₂ ∼ s₁.
    Proof.
        cofix HInd.
        intros s1 s2 H_bsim.
        destruct H_bsim as [s t Hhd Htl].
        constructor; [congruence | exact (HInd _ _ Htl)].
    Qed. 

    Lemma eq_str_trans : 
        forall (s₁ s₂ s₃ : stream A), s₁ ∼ s₂ -> s₂ ∼ s₃ -> s₁ ∼ s₃.
    Proof.
        cofix HInd.
        intros s t u H_bsim1 H_bsim2.
        destruct H_bsim1 as [? ? H_hd1 H_tl1], H_bsim2 as [? ? H_hd2 H_tl2].
        constructor; [congruence | exact (HInd _ _ _ H_tl1 H_tl2)].
    Qed.

    Lemma same_elements_eq_str : 
        forall (s₁ s₂ : stream A),
            (forall i, nth_stream s₁ i = nth_stream s₂ i) -> s₁ ∼ s₂.
    Proof.
        cofix H; intros.
        constructor.    
        -   exact (H0 0).    
        -   assert (forall i : nat, 
                    nth_stream (tl s₁) i = nth_stream (tl s₂) i)
                by (intro i; exact (H0 (S i))).
            exact (H  _ _ H1).
    Qed.

    Lemma eq_str_same_elements : 
        forall (s₁ s₂ : stream A),
            s₁ ∼ s₂ -> (forall i, nth_stream s₁ i = nth_stream s₂ i).
    Proof.
        intros s1 s2 H_bsim i.
        revert s1 s2 H_bsim.
        induction i; intros s1 s2 H_bsim.
        -   inversion H_bsim as [? ? Hhd _]; subst.
            exact Hhd.
        -   inversion H_bsim as [ ? ? _ Htl]; subst.
            exact (IHi _ _ Htl).
    Qed.

End Equiv.

Open Scope stream_scope.

Infix "∼" := eq_str (at level 60, right associativity) : stream_scope. 

Definition unfold_stream {A : Type} (x : stream A) := 
        match x with str a s => str a s end.

Lemma unfold_streamEq : forall (A : Type) (x : stream A), x = unfold_stream x.
Proof.
    destruct x; reflexivity.
Qed.

Add Parametric Relation A : (stream A) (@eq_str A) 
        reflexivity proved by (@eq_str_refl A)
        symmetry proved by (@eq_str_sym A)
        transitivity proved by (@eq_str_trans A) 
        as bisimilar_rel.

Add Parametric Morphism A : (@hd A)
    with signature (@eq_str A) ==> (@eq A) as hd_mor.
Proof.
    intros x y [Ha]; assumption.
Qed.

Add Parametric Morphism A : (@tl A)
    with signature (@eq_str A) ==> (@eq_str A) as tl_mor.
Proof.
    intros x y [Ha]; assumption.
Qed.

Add Parametric Morphism A : (@str A)
    with signature (@eq A) ==> (@eq_str A) ==> (@eq_str A) as str_mor.
Proof.
    intros x s1 s2 H_Eq.
    constructor.
    reflexivity.
    replace (tl (x ⋅ s1)) with s1 by reflexivity.
    replace (tl (x ⋅ s2)) with s2 by reflexivity.
    exact H_Eq.
Qed.

Add Parametric Morphism A : (@nth_stream A)
    with signature (@eq_str A) ==> (@eq nat) ==> (@eq A) as nth_stream_mor.
Proof.
    intros x y Ha n.
    exact (eq_str_same_elements _ _ Ha n).
Qed.

(* Put extensionality in a separated file *)




(*
Lemma hd_eq : forall A (s s' : stream A), s ∼ s' -> hd (s) = hd (s').
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.

Lemma hd_tl : forall A (s s' : stream A), s ∼ s' -> tl (s) ∼ tl (s').
Proof.
    intros.
    rewrite H; reflexivity.
Qed.*)


(* Lemma hd_str : forall A (a : A) (s : stream A), hd (a ⋅ s) = a.
Proof.
    reflexivity.
Defined.

Lemma tl_str : forall A (a : A) (s : stream A), tl (a ⋅ s) = s.
Proof.
    reflexivity.
Qed. *)
