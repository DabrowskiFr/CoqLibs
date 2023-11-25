Require Import Coq.Program.Basics. 
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Morphisms.

Open Scope program_scope.

Require Import Utf8.
From structures.category Require Import Functor.
From structures.category Require Import Monad.

Definition fmap_option {A B : Type} (f : A -> B) (x : option A) :=
  match x with Some y => Some (f y) | None => None end.

Lemma functor_identity_option : forall {A : Type}, fmap_option (@id A) = id.
Proof.
  intros A.
  apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Lemma functor_compose_option :
  forall {A B C: Type} (f : B -> C) (g : A -> B),
    (fmap_option f ∘ fmap_option g) = fmap_option (f ∘ g).
Proof.
  intros A B C f g.
  apply functional_extensionality.
  unfold compose.
  destruct x; reflexivity.
Qed.

Program Instance functor_option : Functor option :=
  {
    fmap A B := @fmap_option A B;
    functor_identity A := @functor_identity_option A;
    functor_compose A B C := @functor_compose_option A B C
  }.

Definition ap_option {A B : Type} (f : option (A -> B)) (x : option A) : option B :=
    match (f, x) with
      (Some f, Some x) => Some (f x)
    | _ => None
    end.


Lemma applicative_identity_option : forall A (x : option A), ap_option (Some id) x = x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma applicative_compose_option :
  ∀ (a b c : Type) (u : option (b -> c)) (v : option (a -> b)) (w : option a) ,
    ap_option (ap_option (ap_option (Some compose) u) v) w = ap_option u (ap_option v w).
Proof.
  destruct u, v, w; reflexivity.
Qed.

Lemma applicative_homomorphism_option :
  ∀ (a b : Type) (f : a -> b) (x : a), ap_option (Some f) (Some x) = Some (f x).
Proof.
  reflexivity.
Qed.

Lemma applicative_interchange_option :
  ∀ (a b : Type) (u : option ( a -> b)) ( y : a),
    ap_option u (Some y) = ap_option (Some ($ y)) u.
Proof.
  destruct u; reflexivity.
Qed.

Lemma applicative_fmap_option : ∀ (A B : Type) (f : A -> B), fmap f  = ap_option (Some f).
Proof.
  reflexivity.
Qed.

Program Instance applicative_option : Applicative option functor_option :=
  {
    pure A  := @Some A;
    ap A B := @ap_option A B;
    applicative_identity := applicative_identity_option;
    applicative_compose := applicative_compose_option;
    applicative_homomorphism := applicative_homomorphism_option;
    applicative_interchange := applicative_interchange_option;
    applicative_fmap := applicative_fmap_option
  }.

Definition bind_option {a b : Type } (x : option a) (f : a ->  option b) :=
      match x with
        Some x => f x
      | None => None
      end.

Lemma monad_left_identity_option : ∀ {a b : Type} (x : a) (k: a -> option b),
    bind_option (Some x) k = k x.
Proof.
  reflexivity.
Qed.

Lemma monad_right_identity_option : forall {a b : Type} (m : option a) , bind_option m Some = m.
Proof.
  destruct m; reflexivity.
Qed.

Lemma monad_associative_option :
  forall {a b c : Type} (m : option a) (k : a -> option b) (h : b -> option c),
    bind_option m (fun x => bind_option (k x) h) = bind_option (bind_option m k) h  .
Proof.
  destruct m; reflexivity.
Qed.

Instance monad_option : Monad option applicative_option :=
  {
    bind a b := @bind_option a b;
    monad_left_identity A B := @monad_left_identity_option A B;
    monad_right_identity A B := @monad_right_identity_option A B;
    monad_associative A B C := @monad_associative_option A B C
  }.


Instance fmap_pointwise_Proper (f : Type -> Type) (E : Functor f) (A B : Type):
  Proper (@pointwise_relation A B eq  ==> eq) fmap.
Proof.
  intros x y H__pointwise.
  f_equal.
  apply functional_extensionality.
  apply H__pointwise.
Qed.

Lemma fmap_some :
  ∀ (A   B : Type) (o : option A) (x : B) (f : A -> B) (H : fmap f o = Some x), ∃ a, o = Some a /\ x = f a.
Proof.
  intros A B o x f H.
  destruct o; simpl in H; [injection H;intros; subst; eauto | discriminate].
Qed.
