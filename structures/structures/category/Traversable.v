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
From structures.category Require Import Functor.
(* From structures.category Require Import Foldable.

(** * Traversable *)
Class Traversable (f : Type -> Type) `(E : Functor f) `(F : Foldable f) : Type :=
  {
    traverse : ∀ (A B : Type) (g : Type -> Type) `(E : Applicative g), (A -> g B) -> f A -> g (f B);
    sequenceA : ∀ (A : Type) (g : Type -> Type) `(E : Applicative g), f (g A) -> g (f A)
  }.
  *)