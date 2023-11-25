CoInductive stream (A : Type) :=
    str : A -> stream A -> stream A.

Arguments str [A].

Definition hd {A : Type} (s : stream A) : A :=
    match s with str a _ => a end.

Definition tl {A : Type} (s : stream A) : stream A :=
    match s with str _ s => s end.

Fixpoint nth {A : Type} (s : stream A) (n : nat) : A :=
    match n with 0 => hd s | S n => nth (tl s) n end.

CoFixpoint map {A B : Type} (f : A -> B) (s : stream A) : stream B :=
    match s with str a s => str (f a) (map f s) end.
