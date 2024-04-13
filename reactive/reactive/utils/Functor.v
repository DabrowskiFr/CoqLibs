From Coq.Classes Require Import RelationClasses.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Category.

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {A B : Type}, (A -> B) -> f A -> f B;
    functor_identity   : forall {A : Type} , fmap (@id A) = id;
    functor_compose : forall {A B C : Type} (g : B -> C) (h : A -> B),
        (fmap g ∘ fmap h) = fmap (g ∘ h)
        (* functor_identity   : forall {A : Type} (a : f A), fmap (@id A) a = a;
    functor_compose : forall {A B C : Type} (g : B -> C) (h : A -> B) (a : f A),
        (fmap g ∘ fmap h) a = fmap (g ∘ h) a *)
  }.

