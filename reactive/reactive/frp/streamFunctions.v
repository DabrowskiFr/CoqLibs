From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses.
From reactive.utils Require Import Algebra.
From reactive.streams Require Import stream.
From reactive.streams Require Import coiteration.

Open Scope type_scope.
Open Scope stream_scope.

(** * Stream functions *)

(** ** Definition *)

(** Stream functions arise from Arrowized FRP, 
    a version of FRP based on arrow combinators.
    A stream function [f : sf A B] receive an input
    of type [A] and produce an output of type [B * sf A B].
    A function over streams of type [A] to streams of type [B]
    for [f : sf A B] is given by [run f : stream A -> stream B]*)

(** * Stream processors *)
(** Generalizing Monads to arrow, John Hugues, 1998 *)
(** data SP a b = Put b (SP a b) | Get (a -> SP a b) *)
(** can be merged *)

CoInductive sf (A B : Set) := SF {step : A -> (B * sf A B)}.

Arguments SF {A B}.
Arguments step {A B}.

CoFixpoint run {A B : Set} : sf A B -> stream A -> stream B :=
    fun f s => 
        match s with 
            str a s' => 
                let (b, f') := step f a in 
                    str b (run f' s') 
        end.

(* toujours la même fonction step *)


Definition make {A B : Set} (f : sf A B) : SFun A B (sf A B) := 
    CoP step f.

(** ** Bisimilarity *)
(** As values of a coinductive type, stream functions
    requires a specific equivalence relation *)

Section Bisimilarity.

    Context {A B : Set}.

    CoInductive bisimilar : relation (sf A B) :=
        bisimilar_act : forall f₁ f₂,
            (forall a b f₁', step f₁ a = (b, f₁') -> 
                exists f₂', step f₂ a = (b, f₂') /\ bisimilar f₁' f₂') -> 
            bisimilar f₁ f₂.

    Lemma bisimilar_refl : forall (f : sf A B), bisimilar f f.
    Proof.
        cofix HInd.
        intros f.
        constructor.
        intros a b f' H_step.
        exists f'; easy.
    Qed.
        
    Lemma bisimilar_sym : forall (f g : sf A B), bisimilar f g -> bisimilar g f.
    Proof.
        cofix HInd.
        intros f g H_bsim.
        inversion H_bsim as [ ? ? Ha Hb]; subst.
        constructor.
        intros a b g' H_step.
        case_eq (step f a); intros c f' H_step'; subst.
        exists f'.
        destruct (Ha _ _ _ H_step') as [g'' [Hc Hd]].
        split.
        -   congruence.
        -   replace g' with g'' by congruence.
            exact (HInd _ _ Hd).
    Qed.
    
    Lemma bisimilar_trans : 
        forall (f g h : sf A B), bisimilar f g -> bisimilar g h -> bisimilar f h.
    Proof.
        cofix HInd.
        intros f g h H_bsim1 H_bsim2.
        constructor.
        intros a b f' H_step1.
        inversion H_bsim1 as [ ? ? Ha]; subst; clear H_bsim1.
        destruct (Ha _ _ _ H_step1) as [g' [Hc Hd]].
        inversion H_bsim2 as [? ? He]; subst; clear H_bsim2.
        destruct (He _ _ _ Hc) as [h' [Hg Hh]].
        exists h'.
        split; [assumption | exact (HInd _ _ _ Hd Hh) ].
    Qed.

    Record bisimulation (R : relation (sf A B)) : Prop :=
        {
            bisim_backward : 
                forall f₁ f₂, R f₁ f₂ ->
                (forall a b f₁', step f₁ a = (b, f₁') -> 
                    exists f₂', step f₂ a = (b, f₂')
                    /\ R f₁' f₂')
        }.

    Context {R : relation (sf A B)} (RBisim : bisimulation R).
        
    Theorem bisimilar_gfp : forall f₁ f₂, R f₁ f₂ -> bisimilar f₁ f₂.
    Proof.
        cofix Hind.
        intros f₁ f₂ H_R.
        destruct RBisim as [Ha].
        constructor.
        intros a b f₁' H_step.
        destruct (Ha _ _ H_R a b f₁' H_step) as [f₂' [Hc Hd]].
        exists f₂'.
        split; [exact Hc | exact (Hind _ _ Hd)].
    Qed.

End Bisimilarity.

Add Parametric Relation A B : (sf A B) (@bisimilar A B) 
        reflexivity proved by (@bisimilar_refl A B)
        symmetry proved by (@bisimilar_sym A B )
        transitivity proved by (@bisimilar_trans A B) 
        as bisimilar_rel.


(** *** Some bisimilarity results *)

Section BisimProp.

    Fact b : forall (A B  : Set) (f : sf A B) (s : stream A), 
        run f s ∼ fst (step f (hd s)) ⋅ run (snd (step f (hd s)))  (tl s).
    Proof.
        intros A B.
        intros f s.
        rewrite (unfold_streamEq _ (run f s)); simpl.
        destruct s as [x s].
        case_eq (step f x); intros; subst; simpl.        
        replace (hd (x ⋅ s)) with x by reflexivity; simpl.
        rewrite H; simpl.
        constructor; reflexivity.
    Qed.

    Lemma run_hd : forall A B (f1 f2 : sf A B) s,
    bisimilar f1 f2 -> hd (run f1 s) = hd (run f2 s).
    Proof.
        intros A B f1 f2 s H_bisim.
        destruct s as [x s].
        inversion H_bisim; subst.
        case_eq (step f1 x); intros; subst.
        destruct (H _ _ _ H0) as [f2' [Ha Hb]].
        rewrite b.
        replace (hd (x ⋅ s)) with x by reflexivity.
        rewrite H0; simpl.
        symmetry.
        rewrite b.
        replace (hd (x ⋅ s)) with x by reflexivity.
        rewrite Ha.
        simpl.
        reflexivity.
    Qed.

End BisimProp.

(** *** Bisimilarity implies semantics equivalence *)

Section BisimEquiv.

    Inductive R_run_eq {A B : Set} : stream B -> stream B -> Prop :=
        | R_run_eqA : forall s (f1 f2 : sf A B),
            bisimilar f1 f2 -> R_run_eq (run f1 s) (run f2 s).

    Lemma R_run_eq_closed : forall A B, eq_str_closed (@R_run_eq A B).
    Proof.
        intros.
        constructor.
        -   intros s1 s2 H_R_run_eq.
            inversion H_R_run_eq; subst; clear H_R_run_eq.
            exact (run_hd _ _ _ _ _ H).
        -   intros s1 s2 H_R_run_eq.
            inversion H_R_run_eq; subst; clear H_R_run_eq.
            destruct s as [x s].
            inversion H; subst.
            case_eq (step f1 x); intros; subst.
            destruct  (H0 _ _ _ H1) as [f' [Ha Hb]].
            rewrite (unfold_streamEq _ (run f1 (x ⋅ s))); simpl.
            rewrite (unfold_streamEq _ (run f2 (x ⋅ s))); simpl.
            rewrite H1.
            rewrite Ha.
            replace (tl (b0 ⋅ run s0 s)) with (run s0 s) by reflexivity.
            replace (tl (b0 ⋅ run f' s)) with (run f' s) by reflexivity.
            apply R_run_eqA.
            apply Hb.
    Qed.

    Proposition run_eq : forall (A B : Set) (f1 f2 : sf A B),
        bisimilar f1 f2 -> forall s, run f1 s ∼ run f2 s.
    Proof.
        intros A B f1 f2 H_bisim s.
        exact (eq_str_gfp (R_run_eq_closed A B) _ _ (R_run_eqA s _ _ H_bisim)).
    Qed.

End BisimEquiv.

(** CoAlbegra *)



(* La relation de bisimulation sur les stream functions 
permet de prouver l'équivalence sémantique de deux streams functions 
sans passer par les traces d'exécution,
si la fonction correspond à un ensemble fini d'état
cela simplifie les choses *)

(* run -> bisim *)

(** ARROWS *)
    
(* SEMANTICS AS BOX *)

(* SEMANTICS AS TRANSITIONS *)
(* AUTOMATON *)
(* iter -> simple function, *)
(* composition ? *)
(* equivalence de fonction comme fonction *)
(* extensionality ???? *)

(* expressivity of YAMPA constructs with respect to SF functions *)
(* completude *)

(* Separate SF from Yampa/arrows construct *)





(** ** Logic *)

(*
Definition valid {A B : Set }(P : formula A) (f : sf A B) (Q : formula B) : Prop :=
    forall s, P s -> Q (eval f s).


Definition realize {A B : Set} (f : sf A B) (g : stream A -> stream B) :=
    forall s, eval f s ∼ g s.
*)
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


(* pour travailler sur des fonctions sur des flux il faut pouvoir faire du filtrage *)
(* ici, on produit element par element *)

(* difference entre map et iter : le registre *)

