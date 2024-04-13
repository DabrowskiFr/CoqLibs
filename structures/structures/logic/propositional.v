From Coq Require Import Setoid.
From mathcomp Require Import fintype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.tuple.
(* From reactive.streams Require Import stream. *)

Require Import Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).

Lemma a : forall A Γ Γ', Included A Γ (Union A Γ Γ').
Proof.
    unfold Included.
    intros.
    apply Union_introl.
    assumption.
Qed.

Lemma b : forall (A : Type) Γ f, f ∈ (Add A Γ f).
Proof.
    intros A Γ f.
    unfold Add.
    apply Union_intror.
    constructor.
Qed.

Module Propositional.

    (* Calcul des propositions *)

    (* Atomes *)

    Parameter A : Type.

    Inductive formula : Type := 
        | Var : A -> formula
        | Ff : formula
        | Imp : formula -> formula -> formula.

    Notation "p ⟶ q" := (Imp p q)(at level 8,right associativity).

    Notation "¬ q" := (q ⟶ Ff)(at level 5,right associativity). 

    Fixpoint model (i : A -> Prop) (f : formula) : Prop :=
        match f with 
            | Var x => i x
            | Ff => False 
            | Imp f g => not (model i f) \/ model i g
        end.

    Definition consequence (Γ : Ensemble formula) (f : formula) :=
        forall (i : A -> Prop), 
            (forall g, g ∈ Γ -> model i g) -> model i f.

    Notation " Γ ⊨ p " := (consequence Γ p) (at level 80).

    (* mp correctness *)
    Lemma consequence_mp : forall Γ f g,
        Γ ⊨ f -> Γ ⊨ f ⟶ g -> Γ ⊨ g.
    Proof.
        unfold consequence.
        intros Γ f g Ha Hb i Hc.
        assert (model i (f ⟶ g)) as Hd by exact (Hb _ Hc).
        inversion Hd as [He | He].
        -   assert (model i f) as Hf by exact (Ha _ Hc).
            exfalso.
            exact (He Hf).
        -   exact He.
    Qed.

    Definition tautology (f : formula) : Prop :=
        (Empty_set formula) ⊨ f.

    (* Hilbert system *)

    (* the pure hilbert system doesn't require 
    Γ, have ⊢ H for all axiom, axiom rule*)
    (* That should be equivalent to having *)
    (* Γ containing exactly the axiom *)
    (* plus the second formulation allows to express 
        consequence *)

    (* Deduction rules *)

    Open Scope type_scope.

    Reserved Notation " Γ ⊢ p " (at level 80).

    Inductive proof (Γ : Ensemble formula) : formula -> Prop :=
        | Ax : forall (p : formula), p ∈ Γ -> Γ ⊢ p
        | MP : forall (p q : formula), Γ ⊢ p -> Γ ⊢ p ⟶ q -> Γ ⊢ q
    where " Γ ⊢ p " := (proof Γ p).

    Lemma weakening : forall {Γ Γ' f}, 
        Included _ Γ Γ' -> Γ ⊢ f -> Γ' ⊢ f.
    Proof.
        intros Γ Γ' f Ha Hb.
        induction Hb as [f | g f _ IH1 _ IH2].
        -   assert (f ∈ Γ') as Hc by now apply Ha.
            apply (Ax Γ' f Hc).
        -   apply (MP Γ' g f IH1 IH2).
    Qed.

    (* Axiom schemes *)

    Inductive Hilbert : formula -> Prop :=
        | Hilbert1 : forall (f g : formula), Hilbert (f ⟶ (g ⟶ f))
        | Hilbert2 : forall (f g h : formula), Hilbert ((f ⟶ (g ⟶ h)) ⟶ ((f ⟶ g) ⟶ (f ⟶ h)))
        | Hilbert3 : forall (f g : formula), Hilbert ((¬ f ⟶ ¬ g) ⟶ (g ⟶ f)).
 
    Definition hilbert Γ := Union _ Hilbert Γ.

    Lemma hilbert_comp : forall Γ, Included formula Hilbert (hilbert Γ).
    Proof.
        apply a.
    Qed.

    Lemma K : forall Γ f g, hilbert Γ ⊢ f ⟶ ( g ⟶ f).
    Proof.
        intros Γ f g.
        apply (weakening (hilbert_comp Γ)).
        apply (Ax _ _ (Hilbert1 f g)).
    Qed.

    Lemma S : forall Γ f g h,
        hilbert Γ ⊢ (f ⟶ (g ⟶ h)) ⟶ ((f ⟶ g) ⟶ (f ⟶ h)).
    Proof.
        intros Γ f g h.
        apply (weakening (hilbert_comp Γ)).
        apply (Ax _ _ (Hilbert2 f g h)).
    Qed.

    (* axiom rule -> apply *)

    Lemma C : forall Γ f g,
        hilbert Γ ⊢ (¬ f ⟶ ¬ g)  ⟶ (g  ⟶ f).
    Proof.
        intros Γ f g.
        apply (weakening (hilbert_comp Γ)).
        apply (Ax _ _ (Hilbert3 f g)).
    Qed.

    Lemma identity : forall Γ f, hilbert Γ ⊢ f ⟶ f.
    Proof.
        intros Γ f.
        assert (hilbert Γ ⊢ f ⟶ ((f ⟶ f) ⟶ f)) as Ha by apply K.
        assert (hilbert Γ ⊢ (f ⟶ ((f ⟶ f) ⟶ f)) ⟶ ((f ⟶ (f ⟶ f)) ⟶ (f ⟶f))) as Hb
               by apply S.
        assert (hilbert Γ ⊢ (f ⟶ (f ⟶ f)) ⟶ (f ⟶ f)) as Hc
            by apply (MP _ _ _ Ha Hb).
        assert (hilbert Γ ⊢ f ⟶ (f ⟶ f)) as Hd
            by apply K.
        apply (MP _ _ _ Hd Hc).
    Qed.        

(* Deduction theorem *)
   
    Theorem deduction : forall Γ f g, 
            Add _ (hilbert Γ) f ⊢ g -> (hilbert Γ) ⊢ f ⟶ g.
    Proof.
        intros Γ f g Ha.
        induction Ha.
        - destruct H as [g Ha | g Ha ].
            +   assert (hilbert Γ ⊢ g) as Hb 
                    by apply (Ax _ _ Ha).
                assert (hilbert Γ ⊢ g ⟶ (f ⟶ g)) as Hc 
                    by apply K.
                apply (MP _ _ _ Hb Hc).
            +   replace g with f by 
                    now (inversion Ha; subst).
                apply identity.
        -   assert (hilbert Γ ⊢ (f ⟶ p) ⟶ f ⟶ q) as Hd.
            {
                assert (hilbert Γ ⊢ (f ⟶ p ⟶ q) ⟶ (f ⟶ p) ⟶ f ⟶ q) as Hc
                    by apply S.
                apply (MP _ _ _ IHHa2 Hc).
            }
            apply (MP _ _ _ IHHa1 Hd).
    Qed.

    (* set auto *)

    Lemma identity_d : forall Γ f, hilbert Γ ⊢ f ⟶ f.
    Proof.
            intros Γ f.
            apply deduction.
            assert (f ∈ (Add formula (hilbert Γ) f)) as Ha 
                by apply b.
            apply (Ax _ _ Ha).
    Qed.

    Theorem correctness : forall Γ f, Γ ⊢ f -> Γ ⊨ f.
    Proof.
        intros Γ f Ha.
        induction Ha.
        -   unfold consequence.
            intros.
            apply H0.
            apply H.
        -   apply consequence_mp with p.
            apply IHHa1.
            apply IHHa2.
    Qed.

    (* Γ finite *)
    Theorem completude : forall Γ f, Γ ⊨ f -> Γ ⊢ f.
    Proof.
        intros Γ f Ha.
        unfold model in Ha.
    Admitted.

    (* Theorem cohérence *)
    (* Theorem decidability *)

    (* Natural deduction *)

    (* interpretation A-algèbre *)
    (* interpretation of varibles -> interpretation of formula *)
End Propositional.
