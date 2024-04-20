From reactive.streams Require Import stream.


Require Import List.
Open Scope list_scope.
Import ListNotations.

Open Scope stream_scope.

Inductive coStream (A St : Set) :=
    Co : (St -> A * St) -> St -> coStream A St.

Arguments Co {A St}.

CoFixpoint run_coStream {A St : Set} : 
    coStream A St -> stream A := 
    fun cs =>
        match cs with 
            Co f x => 
            let (a,y) := f x in 
            str a (run_coStream (Co f y))
        end.

Definition mk_coStream {A : Set} : 
    stream A -> coStream A (stream A) :=
    fun s => 
        Co (fun s => match s with str a s => (a,s) end) s.

Definition CoStreamFunction A St1 B St2 := 
    coStream A St1 -> coStream B St2.

Inductive SFun (T T' St : Set) : Set :=
    CoP : (St -> T -> T' * St) -> St -> SFun T T' St.

Arguments CoP {T T' St}.

Definition runsf {A B St St'} (sf : SFun A B St) : 
    CoStreamFunction A St' B (St * coStream A St') :=
    fun cs => 
    match sf, cs with 
        CoP f_sf st_sf, Co f_i st_i =>
        Co (
            fun (st' : (St  * coStream A St')) => 
            let (s,c) := st' in 
                let (a,st') := f_i st_i in 
                let (b,st) := f_sf st_sf a in 
                (b, (st, Co f_i st'))
        ) (st_sf, cs) 
    end.

Inductive bisim_cstream {A St : Set}  : 
    coStream A St -> coStream A St -> Prop :=
    bisim_ctream_rule : forall f x g y (R : St -> St -> Prop),
        R x y -> 
        (forall x y, exists v x' y', 
            R x y -> f x = (v, x') /\ g y = (v, y') /\ R x' y') ->    
        bisim_cstream (Co f x) (Co g y).

Inductive bisim_sfun {A St1 B St2 : Set}  : 
    SFun A B St1 -> SFun A B St2 -> Prop :=
    bisim_sfun_rule : forall f (x : St1) g (y : St2) (R : St1 -> St2 -> Prop),
        R x y -> 
        (forall x y a, exists v x' y',
            R x y -> f x a = (v,x') /\ g y a = (v,y') /\ R x' y') ->
            bisim_sfun (CoP f x) (CoP g y).

Inductive combinatorial {A B St} : SFun A B St -> Prop :=
    combinatorial_f : forall (sf : SFun A B St) (sg : SFun A B unit),
        bisim_sfun sf sg ->
        combinatorial sf.

(* TypeClass Bisim R *)

(* cstream A St ~ SFun unit A St *)
(* SFun -> CoStreamFunction *)

Definition plus {St₁ St₂ : Set} (cs₁ : coStream nat St₁) (cs₂ : coStream nat St₂): 
    coStream nat (St₁ * St₂) :=     
    match cs₁, cs₂ with 
        Co f x, Co g y => 
            Co (fun s => 
                    let (v₁, s₁') := f (fst s) in 
                    let (v₂, s₂') := g (snd s) in 
                    ((v₁ + v₂)%nat, (s₁',s₂'))
                ) (x,y)
    end.

Definition pre {A St : Set} (v : A) (cs : coStream A St) : coStream A (A *  St) :=
    match cs with 
        Co f x => Co (fun s => (fst s, (f (snd s)))) (v,x)
    end.
    
Definition even {A St : Set} (cs : coStream A St) : coStream A St :=
    match cs with 
        Co f x => 
            Co (fun s => 
                    let (v₁, s₁) := f s in 
                    let (v₂, s₂) := f s₁ in 
                    (v₁, s₂)
            ) x
    end.

Definition dup {A St} (cs : coStream A St) : coStream A ((option A * list A) * St) :=
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

CoFixpoint run {A St : Set} (cs : coStream A St) : stream A := 
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