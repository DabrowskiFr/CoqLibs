(************************************************************************)
(* Copyright 2018 Frédéric Dabrowski                                    *)
(* 
    This program is free software:: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Foobar is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Foobar.  If not, see <https://www.gnu.org/licenses/>.    *)
(************************************************************************)

Require Import Utf8.
Require Import Program.Basics.
Require Import FunctionalExtensionality.
Require Import List.
From structures.category Require Import Functor.
From structures.algebra Require Import Monoid.

Open Scope program_scope.

Inductive Endo_ a := Endo {appEndo : a -> a}.

Inductive Dual_ a := Dual { getDual : a }.

(** * Foldable *)
(*
Instance monoid_dual (A : Type) (E : Monoid A) : Monoid (Dual_ A) :=
  {
    mempty := Dual _ mempty;
    mappend x y := match (x,y) with (Dual _ x, Dual _ y) => Dual _ (mappend x y) end
  }.
Admitted.

Instance monoid_endo (A : Type) : Monoid (Endo_ A) :=
  {
    mempty := Endo _ id;
    mappend x y := match (x,y) with (Endo _ f, Endo _ g) => Endo _ (f ∘ g) end
  }.
Admitted.

Class Foldable (f : Type -> Type) : Type :=
  {
    foldr : ∀ (A B : Type), (A -> B -> B) -> B -> f A -> B;
    foldMap : ∀ (A B : Type) `(E : Monoid B), (A -> B) -> f A -> B :=
      fun _ _ _ f v => foldr _ _ (fun x y => mappend (f x) y) mempty v;
    fold_ : ∀ (A : Type) `(E : Monoid A), f A -> A :=
      fun A _ => foldMap A A _ (fun (x : A) => x);
    foldl : ∀ (A B : Type), (B -> A -> B) -> B -> f A -> B :=
      fun A B f z t => appEndo _ (getDual _ (foldMap _ _ _ (Dual _ ∘ Endo _ ∘ flip f) t)) z;
    to_list : ∀ (A : Type), f A -> list A :=
      fun A v => foldr _ _ (fun x l => List.cons x l) (@List.nil A) v;
    null : ∀ (A : Type), f A -> bool := fun _ v => foldr _ _ (fun _ _ => false) true v;
    length : ∀ (A : Type), f A -> nat := fun A v => foldl _ _ (fun c _ => c+1) 0 v;
  }.

Arguments foldr [f Foldable A B] _ _ _.
Arguments foldMap [f Foldable A B E] _ _.
Arguments fold_ [f Foldable A E] _.
Arguments foldl [f Foldable A B] _ _ _.
Arguments to_list [f Foldable A] _.
Arguments null [f Foldable A] _.
Arguments length [f Foldable A] _.

Instance foldable_option : Foldable option :=
  {
    foldr A B (f : A -> B -> B) (z : B) (o : option A) :=
      match o with
        None => z
      | Some x => f x z 
      end
  }.

Lemma foldable_fold : ∀ A B (E : Monoid B) (g : A -> B) (x : option A),
    @foldMap option foldable_option A B E g x = (@fold_ option foldable_option B E ∘ fmap g) x.
Proof.
  intros A B E g x.
  unfold fold_, foldMap.
  unfold compose.
  destruct x; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma foldable_foldmap : ∀ (A B C : Type) f (E : Monoid C) (F : Functor f) (F : Foldable f)
                           (g : B -> C) (h : A -> B),
    (@foldMap option foldable_option B C E g) ∘ (fmap h) = @foldMap option foldable_option A C E (g ∘ h).
Proof.
  intros A B C f E F F0 g h.
  unfold foldMap.
  unfold compose.
  simpl.
  apply functional_extensionality.
  intros x.
  destruct x; reflexivity.
Qed.*)