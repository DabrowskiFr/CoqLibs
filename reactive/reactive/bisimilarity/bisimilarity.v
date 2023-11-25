(** printing ∼ #&sim;# *)
(** printing ∘ #&#8728; # *)
(** printing ⋅ #&middot; # *)

From reactive.streams Require Import stream.

Require Import Setoid.
Require Import Coq.Program.Basics.

Open Scope program_scope.
(* Open Scope stream_scope. *)

(** ** Bisimilarity *)
(** We define an alternative equivalence relation as a greatest fixpoint. *)
(** intuitively, see P = seq a Q as process that performs a and becomes process *)
Section Bisimilarity.

    Variable A : Set.

    CoInductive bisimilar : stream A -> stream A -> Prop :=
        bisimilar_Seq : forall s1 s2,
            hd s1 = hd s2 -> 
            bisimilar (tl s1) (tl s2) -> bisimilar s1 s2.
End Bisimilarity.

    (* Infix "∼" := bisimilar (at level 60, right associativity) : stream_scope.  *)
(*
    Lemma bisimilar_refl : forall (s : stream A), s ∼ s.
    Proof.
        cofix HInd.
        intro.
        destruct s as [a s].
        constructor.
        -   reflexivity.
        -   exact (HInd s).
    Qed.

    Lemma bisimilar_sym : forall (s1 s2 : stream A), s1 ∼ s2 -> s2 ∼ s1.
    Proof.
        cofix HInd.
        intros.
        destruct H as [s t Hhd Htl].
        constructor.
        -   symmetry; exact Hhd. 
        -   exact (HInd _ _ Htl).   
    Qed. 

    Lemma bisimilar_trans : 
        forall (s1 s2 s3 : stream A), s1 ∼ s2 -> s2 ∼ s3 -> s1 ∼ s3.
    Proof.
        cofix HInd.
        intros s t u HA HB.
        destruct HA as [? ? HAhd HAtl], HB as [? ? HBhd HBtl].
        constructor.
        - congruence.
        - exact (HInd _ _ _ HAtl HBtl).
    Qed.
    
End Bisimilarity.

Arguments bisimilar {A}.

Infix "∼" := bisimilar (at level 60, right associativity) : stream_scope. 


Add Parametric Relation A : (stream A) (@bisimilar A) 
        reflexivity proved by (bisimilar_refl A)
        symmetry proved by (bisimilar_sym A)
        transitivity proved by (bisimilar_trans A) 
        as bisimilar_rel.


(** ** Bisimulation *)
(** A bisimulation is a relation closed by theses rules *)


(** === is the greatest set closed backward by the rules *)
(** This gives us a proof principle *)

Section Bisimulation.

    Variable A : Set.

    Record bisimulation (R : relation (stream A)) : Prop :=
    {
        bisim_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2;
        bisim_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2)
    }.

    Hypothesis R : relation (stream A).
    Hypothesis RBisim : bisimulation R.
    Theorem bisimulation_gfp : forall s1 s2, R s1 s2 -> s1 ∼ s2.
    Proof.
        cofix HInd.
        intros s1 s2 H.
        constructor.
        -   exact (bisim_hd R RBisim s1 s2 H).
        -   apply (HInd (tl s1) (tl s2)).
            exact (bisim_tl R RBisim s1 s2 H).
    Qed.

End Bisimulation.

Arguments bisimulation {A}.
Arguments bisimulation_gfp {A}.
*)