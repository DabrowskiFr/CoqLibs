Fixpoint iterate {D : Type} (f : D -> D) (n : nat) (x : D) : D :=
    match n with 
        | 0 => x 
        | S n => f (iterate f n x)
    end.

Definition image {D1 D2 : Type} (f : D1 -> D2) (P : D1 -> Prop) : D2 -> Prop :=
        fun y => exists x, P x /\ f x = y.

Infix "@" := image (at level 80).
