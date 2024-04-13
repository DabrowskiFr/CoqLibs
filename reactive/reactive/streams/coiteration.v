From reactive.streams Require Import stream.


Require Import List.
Open Scope list_scope.
Import ListNotations.


Open Scope stream_scope.

(* stream process *)
(* (S -> T x S, S) S : state, T : value *)
(* CoStream (T,S) = CoF (S -> T x S, S) *)
(* stream function *)
(* CoStream (T,S) -> CoStream (T',S') *)
(* Synchronous Stream Function *)
(* SFun (T, T', S) = CoP (S -> T -> T' x S, S) *)

(* stream process includes the initial state 
    init, out, trans 
    corresponds to a synchronous stream function, merging out and trans
    *)

(* concrete stream  / coinductive caracterization *)

Inductive cstream (A St : Set) :=
    Co : (St -> A * St) -> St -> cstream A St. 

Arguments Co {A St}.

Definition plus {St₁ St₂ : Set} (cs₁ : cstream nat St₁) (cs₂ : cstream nat St₂): 
    cstream nat (St₁ * St₂) :=     
    match cs₁, cs₂ with 
        Co f x, Co g y => 
            Co (fun s => 
                    let (v₁, s₁') := f (fst s) in 
                    let (v₂, s₂') := g (snd s) in 
                    ((v₁ + v₂)%nat, (s₁',s₂'))
                ) (x,y)
    end.

Definition pre {A St : Set} (v : A) (cs : cstream A St) : cstream A (A *  St) :=
    match cs with 
        Co f x => Co (fun s => (fst s, (f (snd s)))) (v,x)
    end.
    

Definition even {A St : Set} (cs : cstream A St) : cstream A St :=
    match cs with 
        Co f x => 
            Co (fun s => 
                    let (v₁, s₁) := f s in 
                    let (v₂, s₂) := f s₁ in 
                    (v₁, s₂)
            ) x
    end.

Definition dup {A St} (cs : cstream A St) : cstream A ((option A * list A) * St) :=
    match cs with 
        Co f x => 
            Co (
                fun s => 
                    let (v, s') := f (snd s) in   
                        match (fst (fst s)) with 
                            | None => 
                                match (snd (fst s)) with 
                                    | nil => (v, ((Some v, nil), s'))
                                    | cons v' l => (v', ((Some v', app l [v]), s'))
                                end 
                            | Some v0 => (v0, ((None, app (snd (fst s)) [v]), s'))
                        end
            ) ((None, nil), x)
    end.

CoFixpoint run {A St : Set} (cs : cstream A St) : stream A := 
    match cs with 
        Co f x => 
            let (v,y) := f x in 
            str v (run (Co f y))
    end.

Record SyncStreamFunction { A B X : Set } := 
    {
        out : X -> A -> B;
        trans : X -> A -> X;
        init : X
    }.

CoFixpoint iterate {A B X : Set} (out : X -> A -> B) (trans : X -> A -> X) (x : X) : 
    stream A -> stream B := 
    fun s => 
    match s with 
        a ⋅ s' => (out x a) ⋅ (iterate out trans (trans x a) s')
    end.

(* bisimulation *)

(* From A coiterative caracterization of Synchronous Stream Functions *)
(* Co-iteration makes it possible to get rid of recursion *)