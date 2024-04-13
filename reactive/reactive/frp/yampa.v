From Coq.Logic Require Import FunctionalExtensionality.
From reactive.streams Require Import stream.
From reactive.frp Require Import streamFunctions.

Open Scope type_scope.
Open Scope stream_scope.

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

CoFixpoint eval {A B : Set} (f : sf A B) (a : stream A) : stream B := 
match a with 
    a ⋅ s => 
    match step f a with 
        (b, f') => b ⋅ eval f' s
    end
end.

Definition p0 : sf (bool * nat) (nat * nat) :=
    arr (fun (p : bool * nat) => 
            match p with (b,n) => 
                if b then (plus n 1, plus n 1) else (n, 0) end).

Definition p1 : sf bool nat := loop 0 p0.

Definition p2 : sf nat bool :=
    arr (fun n => if Nat.ltb n 5 then true else false). 

(* Catégorie sf : objet types, morphism sf, composition comp *)

(* result on arrows *)


(* sf doit être une catégorie, sf as morphism *)

(* Lemma ar_id : 
    arr id = id. *)

(** ** Bisimulation *)

(* equivalence relation implying bisimilarity *)

Lemma bisim_arrow : forall (A B : Set) (f g : A -> B),
    (forall x, f x = g x) ->
    bisimilar (arr f) (arr g).
Proof.
Admitted.

Lemma bisim_comp : forall A B C 
    (f₁ f₂ : sf A B) (g₁ g₂ : sf B C),
    bisimilar f₁ f₂ -> bisimilar g₁ g₂ -> 
    bisimilar (comp f₁ g₁) (comp f₂ g₂).
Proof.
Admitted.

(* first -> first C *)

Lemma bisim_first : forall (A B C : Set) (f₁ f₂ : sf A B),
    bisimilar f₁ f₂ -> 
    bisimilar (@first A B C f₁) (@first A B C f₂).
Proof.
Admitted.

Lemma bisim_loop : forall (A B C : Set) (c : C) (f₁ f₂ : sf (A * C) (B * C)),
    bisimilar f₁ f₂ ->
    bisimilar (loop c f₁) (loop c f₂).
Proof.
Admitted.


(* More equivalence for transformations *)

(* Elimination des coupures, quelle logique *)

(** ** Co-Itération *)
(* sur les fonctions de flux *)
(* générateurs d'une sf A B ? *)


(* equivalence sur les flux *)

(* toute fonction construite à partir des opérateurs de base est un itérateur *)
(* problème comment exprimer le fait qu'une fonction est construite à partir d'un
itérateur *)

(* est ce que n'est pas vrai tout simplement pour tous les SF ? *)
(* exemples de SF non généré par Yampa *)
(* Tout SF est codé par un générateur *)

(* la nouvelle fonction générée par sf peut elle toujours être exprimée par une fonction d'itération *)
(* contre exemple ???   cv                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  *)



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


(* bisimilarité sur les sf, en coq mais aussi définition formelle de base *)
(* génération aléatoire de la continuation *)
(* sf a b : a-> b, sf a b*)
(* changement de la continuation a chaque fois *)
(* pause d'esterel  ???? *)
(* circuits *)
(* composants de base : arr *)
(* composition séquentielle : comp *)
(* composition parallèle : first *)
(* Pause *)
(* Préemption *)
