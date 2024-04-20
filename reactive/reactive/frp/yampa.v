From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Relations Require Import Relation_Definitions.
From reactive.utils Require Import Category.
From reactive.streams Require Import stream.
From reactive.streams Require Import streamExtensionality.
From reactive.frp Require Import streamFunctions.

Open Scope type_scope.
Open Scope stream_scope.

(** ** Basic Operators *)

CoFixpoint arr {A B : Type} (f : A -> B) : sf A B :=
    SF (fun a => (f a, arr f)).

CoFixpoint comp {A B C : Type} (sf1 : sf B C) (sf2 : sf A B) : sf A C :=
    let f := fun a => 
        let (b, sf2') := step sf2 a in 
        let (c, sf1') := step sf1 b in 
        (c, comp sf1' sf2') 
    in
    SF f.

Notation "A >>> B" := (comp B A) (at level 80, right associativity).

CoFixpoint first {A B C : Type} (f : sf A B) : sf (A * C) (B * C) :=
    let g := fun (ac : A * C) =>
        match (step f (fst ac) : (B * sf A B)) with 
            (b, sf') => ((b,snd ac), first sf' )
        end
    in SF g.

CoFixpoint loop {A B C : Type} (c : C) (f : sf (A * C) (B * C)) : sf A B :=
let f := fun a => 
    match step f (a,c) with 
        ((b,c'), sf') => (b, loop c' sf')
    end
in SF f.
    
(** ** Derived Operators *)

Definition swap {A B : Type} : sf (A * B) (B * A) :=
    arr (fun p => (snd p, fst p)).
    
Definition second {A B C : Type} (f : sf A B) : sf (C * A) (C * B) :=
    comp (comp swap (first f)) swap.

Definition pair {A B C D : Type} (f : sf A B) (g : sf C D) : sf (A * C) (B * D) :=
    (first f) >>> (second g).
     
Notation "A *** B" := (pair A B) (at level 79, right associativity).
     
Definition par {A B C : Type} (f : sf A B) (g : sf A C) : sf A (B * C) :=
    (arr (fun x => (x,x))) >>> (f *** g).

(** ** Evaluation *)

CoFixpoint eval {A B : Type} (f : sf A B) (a : stream A) : stream B := 
match a with 
    a ⋅ s => 
    match step f a with 
        (b, f') => b ⋅ eval f' s
    end
end.

(* (Type, sf)  is a category *)
(*  idty := fun A => arr (idty A);
    compose := @comp *)

(* Foncteur entre les deux catégories Fun_Category et SF_Category *)
Axiom sf_extensionality : forall A B (f g : sf A B),
    bisimilar f g -> f = g.

Inductive R_comp_left_idty {A B : Type} : relation (sf A B) :=
    R_comp_left_idty_1 : 
    forall (f : sf A B),
        R_comp_left_idty (arr (fun x : A => x) >>> f) f.

Lemma R_comp_left_idty_closed : 
    forall A B, bisimulation (@R_comp_left_idty A B).
Proof.
    intros A B.
    constructor.
    intros f₁ f₂ H_R a b f₁' H_step.
    inversion H_R; subst; clear H_R; simpl in H_step.
    case_eq (step f₂ a); intros b0 f₂' HEq.
    rewrite HEq in H_step.
    injection H_step; intros; subst.
    exists f₂'.
    split; [reflexivity | constructor].
Qed.

Lemma comp_left_idty : forall A B (f : sf A B),
    bisimilar (arr (fun x : A => x) >>> f) f.
Proof.
    intros A B f.
    apply (bisimilar_gfp (R_comp_left_idty_closed A B)).
    constructor.
Qed. 

Inductive R_comp_right_idty {A B : Type} : relation (sf A B) :=
    R_comp_right_idty_1 : 
    forall (f : sf A B),
        R_comp_right_idty (f >>> arr (fun x : B => x)) f.

Lemma R_comp_right_idty_closed : 
    forall A B, bisimulation (@R_comp_right_idty A B).
Proof.
    intros A B.
    constructor.
    intros f₁ f₂ H_R a b f₁' H_step.
    inversion H_R; subst; clear H_R; simpl in H_step.
    case_eq (step f₂ a); intros b0 f₂' HEq.
    rewrite HEq in H_step.
    injection H_step; intros; subst.
    exists f₂'.
    split; [reflexivity | constructor].
Qed.


Lemma comp_right_idty : forall A B (f : sf A B),
    bisimilar (f >>> arr (fun x : B => x)) f.
Proof.
    intros A B f.
    apply (bisimilar_gfp (R_comp_right_idty_closed A B)).
    constructor.
Qed.

Inductive R_comp_assoc {A B C D} : relation (sf A D) :=
    R_comp_assoc_1 : 
    forall (f : sf A B) (g : sf B C) (h : sf C D),
        R_comp_assoc ((f >>> g) >>> h) (f >>> g >>> h).

Lemma R_comp_assoc_closed : forall A B C D, 
    bisimulation (@R_comp_assoc A B C D).
Proof.
    intros A B C D.
    constructor.
    intros f₁ f₂ H_R a b f₁' H_step.
    inversion H_R; subst; clear H_R; simpl in H_step.
    case_eq (step f a); intros b0 f' HEq.
    case_eq (step g b0); intros c g' HEq'.
    case_eq (step h c); intros d h' HEq''.
    rewrite HEq, HEq', HEq'' in H_step.
    injection H_step; intros; subst.
    exists (f' >>> g' >>> h').
    split.
    simpl.
    rewrite HEq, HEq', HEq''.
    reflexivity.
    constructor.
Qed.

Lemma comp_assoc : forall A B C D
    (f : sf A B) (g : sf B C) (h : sf C D),
        bisimilar ((f >>> g) >>> h) (f >>> g >>> h).
Proof.
    intros.
    apply (bisimilar_gfp (@R_comp_assoc_closed A B C D)).
    constructor.
Qed.

Program Instance sf_category : Category sf :=
    {
        idty := fun A => arr (idty A);
        compose := @comp
    }.
Next Obligation.
    apply sf_extensionality.
    apply comp_left_idty.
Qed.
Next Obligation.
    apply sf_extensionality.
    apply comp_right_idty.
Qed.
Next Obligation.
    apply sf_extensionality.
    apply comp_assoc.
Qed.

(* (Type, sf) is an arrow *)

(* result on arrows *)


(* sf doit être une catégorie, sf as morphism *)

(* Lemma ar_id : 
    arr id = id. *)

(** ** Bisimulation *)

(* equivalence relation implying bisimilarity *)

Inductive R_bisim_arrow {A B : Type} : relation (sf A B) :=
    R_bisim_arrow_1 : forall (f g : A -> B),
        (forall x, f x = g x) -> R_bisim_arrow (arr f) (arr g).

Lemma R_bisim_arrow_closed : forall A B, bisimulation (@R_bisim_arrow A B).
Proof.
    intros A B.
    constructor.
    intros f1 f2 Ha b c f1' H_step.
    inversion Ha; subst; clear Ha; simpl in H_step.
    injection H_step; intros; subst.
    exists (arr g).
    split; simpl.
    -   congruence.
    -   exact (R_bisim_arrow_1 _ _ H).
Qed. 

Lemma bisim_arrow : forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) ->
    bisimilar (arr f) (arr g).
Proof.
    intros A B f g H.
    exact (bisimilar_gfp (R_bisim_arrow_closed A B) _ _ (R_bisim_arrow_1 f g H)).
Qed.

Inductive R_bisim_comp {A B C : Type} : relation (sf A C) :=
    R_bisim_comp_1 : forall (f₁ f₂ : sf A B) (g₁ g₂ : sf B C),
        bisimilar f₁ f₂ -> bisimilar g₁ g₂ -> 
        R_bisim_comp (comp g₁ f₁) (comp g₂ f₂).

Lemma R_bisim_comp_closed : forall A B C, 
    bisimulation (@R_bisim_comp A B C).
Proof.
    intros A B C.
    constructor.
    intros f1 f2 H_bisim a b f1' H_step.
    inversion H_bisim; subst; clear H_bisim; simpl in H_step.
    inversion H; inversion H0; subst.
    case_eq (step f₁ a); intros. 
    case_eq (step g₁ b0); intros.
    rewrite H2, H3 in H_step.
    injection H_step; intros; subst; clear H_step.
    destruct (H1 _ _ _ H2) as [f2' [Ha Hb]].
    destruct (H4 _ _ _ H3) as [g2' [Hc Hd]].
    exists (f2' >>> g2').
    split; simpl.
    - rewrite Ha, Hc; reflexivity.
    - exact (R_bisim_comp_1 _ _ _ _ Hb Hd).
Qed.
    

Lemma bisim_comp : forall A B C 
    (f₁ f₂ : sf A B) (g₁ g₂ : sf B C),
    bisimilar f₁ f₂ -> bisimilar g₁ g₂ -> 
    bisimilar (comp g₁ f₁ ) (comp g₂ f₂ ).
Proof.
    intros A B C f1 f2 g1 g2 H_bisim1 H_bisim2.
    exact (bisimilar_gfp (R_bisim_comp_closed A B C) _ _ (R_bisim_comp_1 _ _ _ _ H_bisim1 H_bisim2)).
Qed.

(* first -> first C *)

Inductive R_bisim_first {A B C : Type} : relation (sf (A * C) (B * C)) :=
    R_bisim_first_1 : forall (f₁ f₂ : sf A B),
        bisimilar f₁ f₂ ->
        R_bisim_first (@first A B C f₁) (@first A B C f₂).

Lemma R_bisim_first_closed : forall A B C, bisimulation (@R_bisim_first A B C).
Proof.
    intros A B C.
    constructor.
    intros f₁ f₂ H_bisim a b f₁' H_step.
    inversion H_bisim; subst; clear H_bisim; simpl in H_step.
    inversion H; subst.
    case_eq (step f₁0 (fst a)); intros.
    rewrite H1 in H_step.
    injection H_step; intros; subst.
    destruct (H0 _ _ _ H1) as [f₂' [ Ha Hb]].
    exists (@first A B C f₂').
    split; simpl.
    - rewrite Ha; reflexivity.
    - exact (R_bisim_first_1 _ _ Hb).
Qed.

Lemma bisim_first : forall (A B C : Type) (f₁ f₂ : sf A B),
    bisimilar f₁ f₂ -> 
    bisimilar (@first A B C f₁) (@first A B C f₂).
Proof.
    intros A B C f₁ f₂ H_bisim.
    apply (bisimilar_gfp (@R_bisim_first_closed A B C) _ _ (R_bisim_first_1 _ _ H_bisim)).
Qed.

Inductive R_bisim_loop {A B C : Type} : relation (sf A B) :=
    R_bisim_loop_1 : forall (f₁ f₂ : sf (A * C) (B * C)) (c : C),
        bisimilar f₁ f₂ -> 
        R_bisim_loop (loop c f₁) (loop c f₂).

Lemma R_bisim_loop_closed : forall A B C, 
    bisimulation (@R_bisim_loop A B C).
Proof.
    intros A B C.
    constructor.
    intros f₁ f₂ H_bisim a b f₁' H_step.
    inversion H_bisim; subst; clear H_bisim; simpl in H_step.
    inversion H; subst.
    case_eq (step f₁0 (a,c)); intros.
    rewrite H1 in H_step.
    destruct p as [b' c'].
    injection H_step; intros; subst.
    destruct (H0 _ _ _ H1) as [f₂0' [Ha Hb]].
    exists (loop c' f₂0').
    split; simpl.
    -   rewrite Ha; reflexivity.
    -   exact (R_bisim_loop_1 _ _ _ Hb).
Qed.

Lemma bisim_loop : forall (A B C : Type) (c : C) (f₁ f₂ : sf (A * C) (B * C)),
    bisimilar f₁ f₂ ->
    bisimilar (loop c f₁) (loop c f₂).
Proof.
    intros A B C c f₁ f₂ H_bisim.
    exact (bisimilar_gfp (@R_bisim_loop_closed A B C) _ _ (R_bisim_loop_1 _ _ _ H_bisim)).
Qed.

Lemma bisim_second : forall A B (f₁ f₂ : sf A B),
    bisimilar f₁ f₂ ->
    forall C, bisimilar (@second A B C f₁) (@second A B C f₂).
Proof.
    intros A B f₁ f₂ H_bisim C.
    unfold second.
    apply bisim_comp.
    reflexivity.
    apply bisim_comp.
    exact (bisim_first _ _ C f₁ f₂ H_bisim).
    reflexivity.
Qed.

Lemma bisim_pair : forall A B C D (f₁ f₂ : sf A B) (g₁ g₂ : sf C D),
    bisimilar f₁ f₂ -> bisimilar g₁ g₂ -> 
    bisimilar (f₁ *** g₁) (f₂ *** g₂).
Proof.
    intros.
    unfold pair.
    apply bisim_comp.
    apply bisim_first.
    assumption.
    apply bisim_second.
    assumption.
Qed.

Lemma bisim_par : forall A B C (f₁ f₂ : sf A B) (g₁ g₂ : sf A C),
    bisimilar f₁ f₂ -> bisimilar g₁ g₂ ->
    bisimilar (par f₁ g₁) (par f₂ g₂).
Proof.
    intros.
    unfold par.
    apply bisim_comp.
    reflexivity.
    apply bisim_pair; assumption.
Qed.

Inductive R_bisim_comp_arrow_arrow_comp {A B C : Type} : relation (sf A C) :=
    R_bisim_comp_arrow_arrow_comp_1 :
    forall (f : A -> B) (g : B -> C),
    R_bisim_comp_arrow_arrow_comp 
    (arr f >>> arr g) 
    (arr (@compose _ Fun_Category _ _ _ g f )).

Lemma R_bisim_comp_arrow_arrow_comp_closed : forall (A B C : Type),
    bisimulation (@R_bisim_comp_arrow_arrow_comp A B C).
Proof.
    intros A B C.
    constructor.
    intros f₁ f₂ H_bisim a b f₁' H_step.
    inversion H_bisim; subst; clear H_bisim; simpl in H_step.
    injection H_step; intros; subst; clear H_step.
    case_eq (step (arr f) a); intros.
    case_eq (step (arr g) b); intros.
    simpl in H, H0.
    injection H; injection H0; intros.
    exists (arr (@compose _ Fun_Category _ _ _ g f)).
    split.
    reflexivity.
    apply R_bisim_comp_arrow_arrow_comp_1.
Qed.

Lemma bisim_comp_arrow_arrow_comp : forall (A B C : Type)
    (f : A -> B) (g : B -> C),
    bisimilar (arr f >>> arr g) (arr (g ∘ f)).
Proof.
    intros A B C f g.
    exact (bisimilar_gfp (@R_bisim_comp_arrow_arrow_comp_closed A B C) _ _ (R_bisim_comp_arrow_arrow_comp_1 _ _)).
Qed.




(** Programme Yampa *)

(** Toujours une bisimulation en un coup *)
(** seule l'état change *)

(* Stream Functions are arrows *)
(* What special case for Yampa *)


(* Definition pair {A B C D : Set} (f : sf A B) (g : sf C D) : sf (A * C) (B * D) :=
    (first f) >>> (second g).
     
Notation "A *** B" := (pair A B) (at level 79, right associativity).
     
Definition par {A B C : Set} (f : sf A B) (g : sf A C) : sf A (B * C) :=
    (arr (fun x => (x,x))) >>> (f *** g). *)


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
