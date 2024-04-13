
From Coq.Logic Require Import FunctionalExtensionality.

(**  We consider only categories whose objects are Types *)

Class Category : Type :=
    {
        hom : Type -> Type -> Type; 
        idty : forall (A : Type), hom A A;
        compose : forall {A B C : Type}, 
            hom B C -> hom A B ->  hom A C;
        compose_left_idty : forall (A B :Type) (f : hom A B), 
            compose f (idty A) = f;
        compose_right_idty : forall (A B :Type) (f : hom A B), 
            compose (idty B) f = f;
        compose_assoc : forall A B C D
            (f : hom A B) (g : hom B C) (h : hom C D),
            compose h (compose g f) = compose (compose h g) f
    }.

Notation " g ∘ f " := (compose g f)
    (at level 40, left associativity).

Instance Type_Category : Category.
    refine (
        {|
        hom := fun A B => A -> B;
        idty := fun (A : Type) (x : A) => x;
        compose := fun (A B C : Type) (g : B -> C) (f : A -> B) x => g (f x)  
        |}
    ).
Proof.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
    -   intros.
        now apply functional_extensionality.
Defined.

