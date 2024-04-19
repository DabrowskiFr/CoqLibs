(* From reactive.utils Require Import Category. *)
From Coq.Classes Require Import SetoidClass.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Category.

Class Algebra (F : Type -> Type) {H : Functor F}(U : Type) : Type := 
{
    operation : F U -> U
}.

Class CoAlgebra (F : Type -> Type) {H : Functor F} (U : Type) : Type := 
{
    out : U -> F U
}.

(* #[refine] Instance Type_Category : Category := 
{
    Obj := Type;
    Hom := fun A B => A -> B;
    id := fun a x => x;
    compose := fun a b c f g x => g (f x)  
}.
Proof.
   -    intros A B.
        constructor 1 with (equiv := fun (f g : A -> B) => forall x, f x = g x).
        constructor.
        +   intros x.
            reflexivity.
        +   intros x y H.
            easy.
        +   intros x y z Ha Hb.
            congruence.
    -   intros.
        intros f g Ha f' g' Hb x.
        rewrite Ha.
        rewrite Hb.
        reflexivity.
    -   intros.
        constructor.
    -   constructor.
    -   constructor.
Defined.    

(** Specialization over Type *)
(* Definition Type_Functor := @Functor Type_Category Type_Category. *)

Notation EndoFunctor := (fun C => Functor C C).

Class Algebra  (C : Category) (F : Functor C C) (A : Obj C) : Type := 
{
    operation : @Hom C (fobj A) A
}.

Inductive AlgebraF (C : Category) (F : Functor C C) 
    : Type :=
    make_ : forall a : Obj C, 
        Algebra C F a -> AlgebraF C F.

Definition hom_prop {C : Category}
{F : Functor C C}
{U V : Obj C} (A : Algebra C F U)
(B : Algebra C F V) (f : Hom C U V) :=
    f ∘ operation == operation ∘ (fmap f).
    

Class Homomorphism {C : Category} {F : Functor C C}
{U V : Obj C} (A : Algebra C F U) (B : Algebra C F V) := {
    hom : Hom C U V;
    hom_commute : hom_prop A B hom
}.
        

Definition homAlgebraF (C : Category) (F : Functor C C) :
    AlgebraF C F -> AlgebraF C F -> Type.
intros.
inversion X; inversion X0.
exact (Homomorphism X1 X2).
Defined.

#[refine] Instance Algebra_Category (C : Category) 
(F : Functor C C) : Category := 
{
    Obj := AlgebraF C F;
    Hom := _
}.
intro.
inversion C.
unfold Hom.
exact (homAlgebraF C F).


Class Homomorphism {C : Category} {F : Functor C C}
{U V : Obj C} (A : Algebra C F U) (B : Algebra C F V) := {
    hom : Hom C U V;
    hom_commute : hom_prop A B hom
}.

Arguments hom {_ _ _ _ _ _ } _.
    

#[refine] Instance Algebra_Category (C : Category) 
(F : Functor C C) : Category := 
{
    Obj := AlgebraF C F;

}.
intro.
destruct a.        

(** Specialization over Type *)

Definition Type_Algebra := @Algebra Type_Category.



Class Homomorphism {C : Category} {F : Functor C C}
    {U V : Obj C} (A : Algebra C F U) (B : Algebra C F V) := {
        hom : Hom C U V;
        hom_commute : hom_prop A B hom
    }.

Arguments hom {_ _ _ _ _ _ } _.

    Lemma homomorphism_id {C : Category} {F : Functor C C} {U : Obj C} 
    (H : Algebra C F U) : hom_prop H H (id U).
Proof.
    unfold hom_prop.
    rewrite id_left_unit.
    rewrite functor_identity.
    rewrite id_right_unit.
    reflexivity.
Qed.

Definition homomorphism_compose {C : Category} {F : Functor C C} 
    {U V W : Obj C} (HU : Algebra C F U)(HV : Algebra C F V)
    (HW : Algebra C F W) (f : Homomorphism HU HV) 
    (g : Homomorphism HV HW) : Homomorphism HU HW.
    refine ({| hom := 
        (hom g) ∘ (@hom _ _ _ _ _ _ f); hom_commute := _ |}).
    destruct f as [f Hf], g as [g Hg].
    unfold hom_prop in *.
    rewrite functor_compose.
    rewrite compose_assoc.
    rewrite <- Hg.
    rewrite <- compose_assoc.
    rewrite Hf.
    rewrite compose_assoc.
    reflexivity.
Defined.




Definition homomorphism {C : Category}
    {F : Functor C C}
    {U V : Obj C} (A : Algebra C F U)
    (B : Algebra C F V) (f : Hom C U V) :=
        f ∘ operation == operation ∘ (fmap f).

Class CoAlgebra (C : Category) (F : Functor C C) (A : Obj C) : Type := 
{
    out : @Hom C A (fobj A)
}.

Lemma homomorphism_id {C : Category} {F : Functor C C} {U : Obj C} 
    (H : Algebra C F U) : homomorphism H H (id U).
Proof.
    unfold homomorphism.
    rewrite id_left_unit.
    rewrite functor_identity.
    rewrite id_right_unit.
    reflexivity.
Qed.
 *)
(* Examples *)

(* same shape as nat but without recursion, X/nat *)
Inductive Fₓ (X : Type) :=
    Zero : Fₓ X | Succ : X -> Fₓ X.

Definition fmap_Fₓ {X Y : Type } : (X -> Y) -> (Fₓ X -> Fₓ Y) :=  
    fun (f : X -> Y) => 
        fun (x : Fₓ X) => 
        match x with 
            | Zero _ => Zero _ 
            | Succ _ x => Succ _ (f x)
        end.

(* Lemma functor_identity_Fₓ : 
    forall (A : Type), fmap_Fₓ (@id A) == @id (Fₓ A).
Proof.
    intros A a.
    destruct a; reflexivity.
Qed.

Lemma functor_compose_Fₓ : 
    forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap_Fₓ (g ∘ f) == fmap_Fₓ g ∘ fmap_Fₓ f.
Proof.
    intros A B C f g x.
    destruct x; reflexivity.
Qed.

Instance functor_nat : Functor Type_Category Type_Category := {
    fobj := Fₓ;
    fmap := @fmap_Fₓ;
    functor_identity := functor_identity_Fₓ;
    functor_compose := functor_compose_Fₓ
}.

Definition operation_nat : Fₓ nat -> nat :=
    fun x => match x with Zero _ => 0 | Succ _ n => n end.
*)
(* Instance algebra_nat : Algebra Type_Category functor_nat nat := 
{
    operation := operation_nat
}. *)




