
From Coq.Logic Require Import FunctionalExtensionality.


(** * Category theory*)
(** We consider categories whose objects are Types*)

(** ** Category *)

Class Category (hom : Type -> Type -> Type): Type :=
    {

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

Program Instance Fun_Category : Category (fun A B => forall _:A,B) :=
    {|
        idty := fun (A : Type) (x : A) => x;
        compose := fun (A B C : Type) (g : forall _:B, C) (f : forall _:A,B) x => g (f x)  
    |}.
Next Obligation.
    intros.
    now apply functional_extensionality.
Qed.
Next Obligation.
    intros.
    now apply functional_extensionality.
Qed.
Next Obligation.
    intros.
    now apply functional_extensionality.
Qed.

(** ** Functor *)

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {A B : Type}, (A -> B) -> f A -> f B;
    functor_identity   : forall {A : Type} , fmap (idty A) = idty (f A);
    functor_compose : forall {A B C : Type} (g : B -> C) (h : A -> B),
        (fmap g ∘ fmap h) = fmap (g ∘ h)
  }.

Program Instance Idty_Functor : Functor (fun x => x) := 
    {| 
        fmap := fun A B (f : A -> B) => f;
    |}.
Next Obligation.
reflexivity.
Qed.
Next Obligation.
reflexivity.
Qed.

(** Applicative Programming with Effects, Conor McBride and Ross Paterson, 2008 **)

Class Applicative (f : Type -> Type) `{H : Functor f} : Type :=
    {
        pure : forall {A : Type}, A -> f A;
        app : forall {A B : Type}, f (A -> B) -> f A -> f B;
        applicative_idty : forall {A : Type} (a : f A), app (pure (idty A)) a = a;
        applicative_compose : 
            forall {A B C : Type} (u : f (B -> C)) (v : f (A -> B)) (w : f A),
            app (app (app (pure (compose)) u) v) w = app u (app v w);
        applicative_homomorphism : forall A B (h : A -> B) (x : A),
            app (pure h) (pure x) = pure (h x);
        applicative_interchange : forall A B (h : f (A -> B)) (x : A),
            app h (pure x) = app (pure (fun f => f x)) h 
    }.

Program Instance Idty_Applicative : Applicative (fun x => x) :=
    {| 
        pure := fun A (a : A) => a;
        app := fun (A B : Type) (h : A -> B) (x : A) => h x 
    |}.
Next Obligation.
    reflexivity.
Qed.
Next Obligation.
    reflexivity.
Qed.
Next Obligation.
    reflexivity.
Qed.
Next Obligation.
    reflexivity.
Qed.

(* -> Category *)

Lemma applicative_fmap : forall (m : Type -> Type) (H : Functor m) (H1 : Applicative m) 
    A B (f:A -> B)  (x : m A), 
    fmap f x = app (pure f) x.
Proof.
Admitted.

(** ** Monad *)
(** Comprehending monads, P. L. Wadler, 1990  *)

Class Monad (m : Type -> Type) `{F : Applicative m} : Type :=
{
  (* ret : forall {A}, A -> m A; *)
    bind : forall {A B}, m A -> (A -> m B) -> m B;
    monad_left_idty : forall A B (a : A) (f : A -> m B), bind (pure a) f = f a;
    monad_right_idty : forall A (m : m A), bind m pure = m;
    monad_associativity : forall A B C (x : m A) (f : A -> m B) (g : B -> m C), 
        bind x (fun y => bind (f y) g) = bind (bind x f) g;
    monad_app : forall A B (m1 : m(A -> B)) (m2 : m A),
        app m1 m2 = bind m1 (fun x1 => bind m2 (fun x2 => pure (x1 x2))) 
}.

Program Instance Idty_Monad : Monad (fun x => x) := 
    {|
    bind := fun A B m f => f m;
    |}.
Next Obligation.
    reflexivity.
Qed.
Next Obligation.
reflexivity.
Qed.
Next Obligation.
reflexivity.
Qed.
Next Obligation.
reflexivity.
Qed.

(* Monad => Applicative *)
(* Applicative => Functor *)

Lemma monad_fmap : forall (m : Type -> Type) 
    (H0 : Functor m) (H1 : Applicative m) (H : Monad m) 
    (A B : Type) (f : A -> B) (x : m A),
    fmap f x = bind x (pure ∘ f).
Proof.
Admitted.

(** ** Arrows *)
(** generalizing monads to arrows, John  Hughes, 1998 *)

Class Arrow (sf : Type -> Type -> Type) `{Cat : Category sf}: Type := 
{
  arr : forall {A B}, (A -> B) -> sf A B;
  first : forall {A B C}, sf A B -> sf (A * C)%type (B * C)%type;
  arr_id : forall A, arr (idty A) = idty A ;
  arr_comp : forall A B C (g : B -> C) (f : A -> B), 
    arr (g ∘ f) = (arr g) ∘ (arr f); 
  first_comp : forall A B C D (g : sf B C) (f : sf A B),  
    @first A C D (g ∘ f) = (first g) ∘ (first f);
  (* first_comp2 : forall A B C (f : @hom Cat A (B * C)),
    @first A B C f ∘ arr fst = arr fst ∘ f *)
}.

Program Instance Fun_Arrow : Arrow (fun A B => A -> B) :=
{|
    arr := fun A B (f : A -> B) => f;
    first := fun A B C f => fun p => let (b,c) := p in (f b, c)
|}.
Next Obligation.
reflexivity.
Qed.
Next Obligation.
reflexivity.
Qed.
Next Obligation.
intros.
apply functional_extensionality.
destruct x; reflexivity.
Qed.
