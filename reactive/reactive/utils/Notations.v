(* Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x). *)


(* Definition id {A : Type} : A -> A := fun x => x. *)

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C := fun x y => f y x.

Definition const {A B} (a: A) := fun (x : B) => a. 
  
