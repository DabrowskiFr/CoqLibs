Require Import Coq.Logic.FunctionalExtensionality.
From reactive.streams Require Import stream.
From reactive.ltl Require Import ltl.
From reactive.bisimilarity Require Import bisimilarity.
Open Scope type_scope.

(** ** Stream function *)

CoInductive sf (A B : Set) := 
    SF {step : A -> (B * sf A B)}.

    (* génération aléatoire de la continuation *)
    (* sf a b : a-> b, sf a b*)
    (* changement de la continuation a chaque fois *)
    (* pause d'esterel  ???? *)
Arguments SF {A B}.
Arguments step {A B}.

(* circuits *)
(* composants de base : arr *)
(* composition séquentielle : comp *)
(* composition parallèle : first *)
(* Pause *)
(* Préemption *)

(** ** Basic Operators *)

CoFixpoint arr {A B : Set} (f : A -> B) : sf A B :=
    SF (fun a => (f a, arr f)).

CoFixpoint comp {A B C : Set} (sf1 : sf A B) (sf2 : sf B C) : sf A C :=
    let f := fun a => 
        let (b, sf1') := step sf1 a in 
        let (c, sf2') := step sf2 b in 
        (c, comp sf1' sf2') 
    in
    SF f.

Notation "A >>> B" := (comp A B) (at level 80, right associativity).

CoFixpoint first {A B C : Set} (f : sf A B) : sf (A * C) (B * C) :=
    let g := fun (ac : A * C) =>
        match (step f (fst ac) : (B * sf A B)) with 
            (b, sf') => ((b,snd ac), first sf' )
        end
    in SF g.

CoFixpoint loop {A B C : Set} (c : C) (f : sf (A * C) (B * C)) : sf A B :=
let f := fun a => 
    match step f (a,c) with 
        ((b,c'), sf') => (b, loop c' sf')
    end
in SF f.
    
(** ** Derived Operators *)

Definition swap {A B : Set} : sf (A * B) (B * A) :=
    arr (fun p => (snd p, fst p)).
    
Definition second {A B C : Set} (f : sf A B) : sf (C * A) (C * B) :=
    comp (comp swap (first f)) swap.

Definition pair {A B C D : Set} (f : sf A B) (g : sf C D) : sf (A * C) (B * D) :=
    (first f) >>> (second g).
     
Notation "A *** B" := (pair A B) (at level 79, right associativity).
     
Definition par {A B C : Set} (f : sf A B) (g : sf A C) : sf A (B * C) :=
    (arr (fun x => (x,x))) >>> (f *** g).


(** ** Evaluation *)
(*
CoFixpoint eval {A B : Set} (f : sf A B) (a : stream A) : stream B := 
match a with 
    a ⋅ s => 
    match step f a with 
        (b, f') => b ⋅ eval f' s
    end
end.

(** ** Logic *)

Definition valid {A B : Set }(P : formula A) (f : sf A B) (Q : formula B) : Prop :=
    forall s, P s -> Q (eval f s).


Definition realize {A B : Set} (f : sf A B) (g : stream A -> stream B) :=
    forall s, eval f s ∼ g s.

(* eval n'est pas un map, plutôt un fold *)



(* l'information au temps n ne dépend pas de > n *)
(* en coq on peut pas écrire de telles fonctions mais on ne peut pas l'exploiter 
dans les preuves *)

(* f (s) = g (hd s) :: h (hd s?) (tl s) *)


(* rewrite equiv *)
(* Lemma arr_realize {A B : Set} : forall (f : A -> B),
    realize (arr f) (map f).
Proof.
Admitted. *)

(* flux d'entrée ? *)
(* sur les flux*)
(* Definition Stream_coiter : forall {A X:Set}, (X -> A) -> (X -> X) -> X -> stream A. *)

(** ** Co-Itération *)
(* sur les fonctions de flux *)
(* générateurs d'une sf A B ? *)
CoFixpoint iterate {A B X : Set} (out : X -> A -> B) (trans : X -> A -> X) (x : X) : 
    stream A -> stream B := 
    fun s => 
    match s with 
        a ⋅ s' => (out x a) ⋅ (iterate out trans (trans x a) s')
    end.

(* pour travailler sur des fonctions sur des flux il faut pouvoir faire du filtrage *)
(* ici, on produit element par element *)

(* difference entre map et iter : le registre *)

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


(* equivalence sur les flux *)

(* toute fonction construite à partir des opérateurs de base est un itérateur *)
(* problème comment exprimer le fait qu'une fonction est construite à partir d'un
itérateur *)

(* est ce que n'est pas vrai tout simplement pour tous les SF ? *)
(* exemples de SF non généré par Yampa *)
(* Tout SF est codé par un générateur *)

(* la nouvelle fonction générée par sf peut elle toujours être exprimée par une fonction d'itération *)
(* contre exemple ???   cv                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  *)

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

(* yampa récursive loop *)
    

(* fonction input -> min, max, average *)
(* remise à zéro *)

(* troufer out et trans à partir de A -> (B, sf A B) *)
(* non SF A B reste une fonction sur les flux, pas un itérateur *)

(* On fait remonter les loops !!! *)
(* On peut tout écrire avec un loop appliqué à une fonction d'itération *)
(* En soit un résultat *)


(* Version Monad ??? *)    
    (* equivalence YAMPA ~emap ??? *)
    (* emap ~ loop ??? *)

(* map : pas suffisant pour la boucle -> iter *)

(*Definition Stream_coiter : forall X:Set, (X -> A) -> (X -> X) -> X -> Stream.*)

(* on peut observer complétement les streams dans les propriétés mais pas dans les fonctions 
    P(s) = s ne contient que des 1, f (s) = true ssi s ne contient que des 1 *)
(* on peut observer une propriété infinie, si la chaine infinie contient un motif de répétition *)

(* notion de realisabilité trop faible, il faut restreindre l'observation de l'entrée *)
(* f : sream A -> stream B fonction out : in -> reg -> (b, reg), next : in -> reg -> stream b *)

(* map (in -> out) *)
(* iterate (in, reg -> out, reg) *)
(* => State Monad *)
(* Iterate (M in -> M out), read au début, write à la fin ==> arrow ? *)
(* Ma -> Mb | Mc -> Md : composer les états dans M ?? M(a,c) -> M (b,d)*)
(* iter function out, next *)
(* nth n (f s) = f' (first n s) *)
(* répétition d'une fonction sur les listes finies *)
(* contre exemple : est ce s contient 0 *)

(* detecte si contient la valeur 1 3 fois séparés par au plus 2 temps *)



(* loop ~ unfold *)

(* equivalence entre sf a b et stream a -> stream b *)
(* PAsser d'une equivalence sur les stream function au stream permet d'élimier le coté 
récursif des fonctions de flux *)


(* somme des valeurs du flux *)

(* Propriétés sur les flux *)
(* La propriétés de sortie à un certain rang ne dépend que 
des rangs précédents *)

(* si entrée dépasse un certain seuil, sortie désactivé *)
(* parallèle si entrée désactivée, remize à zéro *)

(* compteur incrémenté à chaque ittération, remis à 0 si >= N *)

Definition p0 : sf (bool * nat) (nat * nat) :=
    arr (fun (p : bool * nat) => 
            match p with (b,n) => 
                if b then (plus n 1, plus n 1) else (n, 0) end).

Definition p1 : sf bool nat := loop 0 p0.

Definition p2 : sf nat bool :=
    arr (fun n => if Nat.ltb n 5 then true else false). 

(* bisimilarité sur les sf, en coq mais aussi définition formelle de base *)
*)