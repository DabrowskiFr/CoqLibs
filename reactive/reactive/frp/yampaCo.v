Require Import Coq.Logic.FunctionalExtensionality.
From reactive.streams Require Import stream.
From reactive.streams Require Import coiteration.
From reactive.frp Require Import streamFunctions.
From reactive.frp Require Import yampa.

    (** ** Yampa operators are co-iterators *)
    Definition arr_iter {A B : Set} (f : A -> B) (X : Set) : X -> stream A -> stream B :=
        iterate (fun _ a => f a) (fun x _ => x).
    
    (* la composition ne compose pas les registres *)
    
    Definition comp_iter {A B C X Y : Set} 
        (fout : X -> A -> B) (ftrans : X -> A -> X) 
        (gout : Y -> B -> C) (gtrans : Y -> B -> Y)  : X * Y -> stream A -> stream C :=
        iterate (fun p a => match p with (x, y) => gout y (fout x a) end)
            (fun p a => match p with (x, y) => (ftrans x a, gtrans y (fout x a)) end).
            
    Definition first_iter {A B C X : Set} (fout : X -> A -> B) (ftrans : X -> A -> X): 
        X -> stream (A * C) -> stream (B * C) :=
        iterate (fun x p => match p with (a,c) => (fout x a, c) end )
        (fun x p => match p with (a,c) => ftrans x a end).
    
    (* a t'on vraiment besoin de définir loop_iter *)
    Definition loop_iter {A B C X : Set} (fout : X -> A -> B) (ftrans : X -> A -> X) :
        X -> stream A -> stream B := iterate fout ftrans.
    
    Inductive RArr {A B : Set} (f : A -> B) (X : Set) : stream B -> stream B -> Prop :=
        RArra : forall (x : X) s,
            RArr f X (eval (arr f) s) (iterate (fun _ a => f a) (fun x _ => x) x s).
    
    (*
    Fact bisimulation_RArr : 
        forall (A B : Set) (f : A -> B) (X : Set),
        bisimulation (RArr f X).
    Proof.
        constructor.
        -   intros s1 s2 [x [a s]].
            reflexivity.
        -   intros s1 s2 [x [a s]].
            exact (RArra f X x s).
    Qed.
    
    Lemma sf_iter_arr : forall {A B : Set} (f : A -> B) (X : Set) (x : X) (s : stream A),
        eval (arr f) s ∼ iterate (fun _ a => f a) (fun x _ => x) x s.
    Proof.
        intros.
        exact (bisimulation_gfp _ (bisimulation_RArr _ _ f X) _ _ (RArra f X x s)).
    Qed.
    
    (* Definition sf_iter (f : sf A B) (out : ) (trans : ) (x : X)
        forall s, eval sf s === iterate out trans x s *)
    
    Lemma sf_iter_comp : forall {A B C : Set} (sf1 : sf A B) (sf2 : sf B C)
    (X : Set) fout ftrans gout gtrans  (x y : X),
        (forall s, eval sf1 s ∼ iterate fout ftrans x s) ->
        (forall s, eval sf2 s ∼ iterate gout gtrans x s) ->
        forall s, eval (sf1 >>> sf2) s ∼ 
        iterate (fun p a => match p with (x, y) => gout y (fout x a) end)
            (fun p a => match p with (x, y) => (ftrans x a, gtrans y (fout x a)) end) (x,y) s.
    Admitted.
    
    Lemma sf_iter_first : forall {A B C : Set} (sf : sf A B) (X : Set)
        (out : X -> A -> B) (trans : X -> A -> X) (x : X) ,
        (forall s, eval sf s ∼ iterate out trans x s) ->
        forall (s : stream (A * C)), eval (first sf) s ∼ 
            iterate (fun x p => match p with (a,c) => (out x a, c) end )
            (fun x p => match p with (a,c) => trans x a end) x s.
    Admitted.
    
    (* Lemma sf_iter_loop : forall {A B X Y : Set} (f : sf (A * X) (B * X))
        (out : Y -> (A * X) -> (B * X)) (trans : Y -> (A * X) -> Y) 
        (x : X) (y : Y),
        (forall s, eval f s ∼ iterate out trans y s) -> 
        forall (s : stream A), eval (loop x f) s ∼
            iterate (fun a p => match p with (x,y) => out y (a,x) end) 
                (fun a p => match p with (x,y) => (x, trans y (a,x)) end ) (x,y) s .
     *)
    
    Proposition all_iter : forall (A B : Set) (f : sf A B), 
    exists (X : Set) out trans (x : X), 
        forall (s : stream A), eval f s ∼ iterate out trans x s.
Proof.
    
Abort.
(* tout sf peut s'exprimer par yampa / iter *)
(* tout yampa peut s'exprimer par sf / iter*)

Inductive Yampa : forall (A B : Set), sf A B -> Prop :=
    | YampaArr : forall (A B  : Set) (f : A -> B), Yampa A B (arr f)
    | YampaCom : forall (A B C : Set) sf1 sf2, Yampa A B sf1 -> Yampa B C sf2 -> Yampa A C (comp sf1 sf2)
    | YampaFirst : forall (A B C : Set) sf, Yampa A B sf -> Yampa (A * C) (B * C) (first sf)
    | YampaLoop : forall (A B X : Set) (x : X) (sf : sf (A * X) (B * X)), 
        Yampa (A * X) (B * X) sf -> Yampa A B (loop x sf).

Arguments Yampa {A B}.

Require Import Coq.Program.Equality.

Proposition all_iter : forall (A B : Set) (f : sf A B),
    Yampa f -> 
    exists (X : Set) out trans (x : X), 
        forall (s : stream A), eval f s ∼ iterate out trans x s.
Proof.
    intros.
    dependent induction H.
    -   exists unit.
        exists (fun _ a => f a).
        exists (fun x _ => x).
        exists tt.
        intro s.
        apply sf_iter_arr.
    -   destruct IHYampa1 as [X [fout [ftrans [x Hx]]]].
        destruct IHYampa2 as [Y [gout [gtrans [y Hy]]]].
        exists (X * Y).   
        exists (fun p a => match p with (x, y) => gout y (fout x a) end).
        exists (fun p a => match p with (x, y) => (ftrans x a, gtrans y (fout x a)) end).
        exists (x,y).
        intro s.
        admit.
    -   destruct IHYampa as [X [out [trans [x Hx]]]].
        exists X.
        exists (fun x p => match p with (a,c) => (out x a, c) end ).
        exists (fun x p => match p with (a,c) => trans x a end).
        exists x.
        intro s.
        admit.
    -   destruct IHYampa as [Y [out [trans [y Hy]]]].
        exists (X * Y).
        admit.
Admitted.
*)