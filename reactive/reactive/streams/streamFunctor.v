From reactive.utils Require Import Category.
From reactive.utils Require Import Functor.
From reactive.streams Require Import stream.
From reactive.streams Require Import streamExtensionality.

CoFixpoint stream_map {A B : Type} (f : A -> B) : stream A -> stream B :=
    fun s => match s with str a s => str (f a) (stream_map f s) end.

    Inductive stream_Functor_R (A : Type) : stream A -> stream A -> Prop :=
        stream_Functor_RA : 
            forall s, stream_Functor_R A (stream_map id s) s. 

    (* Category *)
    Inductive stream_Functor_R2 (C : Type) : stream C -> stream C -> Prop :=
        stream_Functor_R2A : 
            forall (A B : Type) (s : stream A) (f : A -> B) (g : B -> C), 
            stream_Functor_R2 C 
            (((stream_map g) ∘ (stream_map f)) s) 
            (* (stream_map (@compose Type_Category _ _ _ g f) s). *)
            (stream_map (g ∘ f) s).
    
    Lemma eq_str_closed_Functor_R : 
        forall (A : Type), eq_str_closed (stream_Functor_R A).
    Proof.
        constructor.
        -   intros s1 s2 H.
            inversion H; subst.
            rewrite (unfold_streamEq _ (stream_map id s2)).
            destruct s2; reflexivity.
        -   intros s1 s2 H.
            inversion H; subst.
            rewrite (unfold_streamEq _ (stream_map id s2)).
            destruct s2.
            apply stream_Functor_RA.
    Qed.
    
            
    Instance stream_Functor : Functor stream.
    refine (
    {|
        fmap := @stream_map
    |}).
    Proof.
    -   intros.
        apply stream_extensionality.
        (* exact (eq_str_gfp (eq_str_closed_Functor_R A) _ _ (stream_Functor_RA _ _)). *)
        Admitted.
    (* -   intros.
    Admitted. *)
        (* apply H.
        exact (stream_Functor_RA _ _). *)