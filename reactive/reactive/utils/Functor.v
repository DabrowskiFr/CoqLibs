From Coq.Classes Require Import RelationClasses.
From reactive.utils Require Import Notations.
From reactive.utils Require Import Category.

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {A B : Type}, (A -> B) -> f A -> f B;
    functor_identity   : forall {A : Type} , fmap (@id A) = id;
    functor_compose : forall {A B C : Type} (g : B -> C) (h : A -> B),
        (fmap g ∘ fmap h) = fmap (g ∘ h)
  }.

(* Monad laws : P. L. Wadler. Comprehending monads.*)
Class Monad (m : Type -> Type) `{F : Functor m} : Type :=
{
  ret : forall {A}, A -> m A;
  bind : forall {A B}, m A -> (A -> m B) -> m B;
  monad_prop1 : forall A B (a : A) (f : A -> m B), bind (ret a) f = f a;
  monad_prop2 : forall A (m : m A), bind m ret = m;
  monad_prop3 : forall A B C (x : m A) (f : A -> m B) (g : B -> m C), 
    bind x (fun y => bind (f y) g) = bind (bind x f) g
}.

(* Category based on the category on type and functions *)
Class Arrow `{Cat : Category}: Type := 
{
  arr : forall {A B}, @hom Type_Category A B -> @hom Cat A B;
  first : forall {A B C}, @hom Cat A B -> @hom Cat (A * C)%type (B * C)%type;
  arr_id : forall A, arr (@id A) = @idty Cat A;
  arr_comp : forall A B C (g : @hom Type_Category B C) (f : @hom Type_Category A B), 
    arr (g ∘ f) = (arr g) ∘ (arr f); 
  first_comp : forall A B C D (g : @hom Cat B C) (f : @hom Cat A B),  
    @first A C D (g ∘ f) = (first g) ∘ (first f);
  (* first_comp2 : forall A B C (f : @hom Cat A (B * C)),
    @first A B C f ∘ arr fst = arr fst ∘ f *)
}.

(* Instance arrowCat (A : Arrow) : Category :=
{
  
}.
constructor. *)

(* Loop arrow *)

(* Category *)
(* Class Arrow (a : Type -> Type -> Type) `{C : Category}: Type := 
{
  arr : forall {A B}, (A -> B) -> a A B;
  seq : forall {A B C}, a A B -> a B C -> a A C;
  first : forall {A B C}, a A B -> a (A * C)%type (B * C)%type;
  arr_id : arr id = id
}. *)