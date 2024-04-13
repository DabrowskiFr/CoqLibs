Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Compare_dec.


Fixpoint iterate {D : Type} (f : D -> D) (n : nat) (x : D) : D :=
    match n with 
        | 0 => x 
        | S n => f (iterate f n x)
    end.

Definition image {D1 D2 : Type} (f : D1 -> D2) (P : D1 -> Prop) : D2 -> Prop :=
        fun y => exists x, P x /\ f x = y.

Infix "@" := image (at level 80).

Section Directed.

    Variable D : Type.
    Variable eqD : relation D.
    Variable R : relation D.

    Infix "⊑" := R (at level 80).

    Definition directed (P : D -> Prop) :=
        forall x y, P x -> P y -> exists z, x ⊑ z /\ y ⊑ z.

    Definition chain (P : D -> Prop) := forall x y, 
        P x -> P y -> x ⊑ y \/ y ⊑ x.

    Context `{R_PartialOrder : PartialOrder D eqD R}.

    Lemma chaindirected : forall P, chain P -> directed P.
    Proof.
        unfold directed, chain. 
        intros P HChain x y HPx HPy.
        destruct (HChain x y HPx HPy).
        exists y; split; [assumption | reflexivity].
        exists x; split; [reflexivity | assumption].
    Qed.

End Directed.

Arguments directed {D}.
Arguments chain {D}.

Section Directed_Example.

    Definition pnat := (fun n : nat => True).

    Lemma directedNatLe : directed le pnat.
    Proof.
        intros.
        assert (chain le pnat).
        {
            intros x y _ _.
            destruct (le_ge_dec x y); auto.
        }
        now apply (chaindirected nat le pnat).
    Qed.

End Directed_Example.

Section Monotonic2.

    Context `{D1 : Type}.
    Context `{D2 : Type}.
    Context {R1 : D1 -> D1 -> Prop}.
    Context {R2 : D2 -> D2 -> Prop}.

    (* Infix "⊑" := R1 (at level 80).
    Infix "≼" := R2 (at level 80). *)

    Class Monotonic2 (f : D1 -> D2) : Type :=
       monotonicity2 : forall x y, R1 x y -> R2 (f x) (f y).
        
End Monotonic2. 

Class Monotonic (D : Type) (R1 : D -> D -> Prop) 
    (E : Type) (R2 : E -> E -> Prop) (f : D -> E) 
    `{PartialOrder D eq R1} `{PartialOrder E eq R2} :=
    monotonicity : forall x y, R1 x y -> R2 (f x) (f y).

Section Monotonic_Example.

    Definition succ := fun x => S x.

    Global Instance MonotonicS : Monotonic nat le nat le succ.
    Proof.
        intros x y H.
        unfold succ.
        auto.
        intuition.
    Qed.

    Lemma a : le (succ 0) (succ 0).
    Proof.
        apply monotonicity.
        intuition.
    Qed. 


End Monotonic_Example.




Class DCPO D eqD  R lub `{PartialOrder D  eqD R} := 
{
    lub_prop0 : forall P, exists y, lub P y;
    lub_prop1 : forall x y P, lub P x -> lub P y -> eqD x y;
    lub_prop2 : forall (P : D -> Prop) y z, directed R P -> P y -> lub P z -> R y z;
    lub_prop3 : forall (P : D -> Prop) y z , directed R P -> 
        (forall x, P x -> R x y) -> lub P z -> R z y
}.

    

Class CPO D eqD R lub bot `{DCPO D eqD R lub} := 
    bot_prop : forall x, R bot x.

Section TestCPO.

    (* Definition lub :=   *)
    (* lub ???? --> property + version spécifique fonction *)

    (* Global Instance A : CPO nat_bot (@eq nat_bot) ble  *)
End TestCPO.
(*
Section DirectedPreservation.

    Variable D1 : Type.
    Variable eqD1 : relation D1.
    Variable R1 : relation D1.
    Variable D2 : Type.
    Variable eqD2 : relation D2.
    Variable R2 : relation D2.
    Variable f : D1 -> D2.
    Infix "⊑" := R1 (at level 80).
    Infix"≼" := R2 (at level 80).

    Context `{R1_PartialOrder : PartialOrder D1 eqD1 R1}.
    Context `{R2_PartialOrder : PartialOrder D2 eqD2 R2}.
    Context `{Monotonic D1 R1 D2 R2 f}.

    Lemma monotonicity_directed : 
        forall P ,
        directed R1 P -> directed R2 (image f P).
    Proof.
        unfold directed.
        intros P Ha x y [x0 [Hb Hc ]] [y0 [Hd He ]].
        destruct (Ha x0 y0 Hb Hd) as [z [Hh Hi]].
        subst.
        exists (f z).
        split; now apply monotonicity with (R1 := R1).
Qed.

End DirectedPreservation.


    Section A.
    Variable D : Type. 
    Variable eqD : relation D.
    Variable R : relation D.
    Variable f : D -> D. 

    Infix "⊑" := R (at level 80).

    Context `{Monotonic D R D R f}.
    Context `{Cpo : CPO D eqD R}. 

    Notation "⊥" := (bot D eqD R).

    Lemma iterate_prop : 
        forall n m, m <= n ->
        iterate f m ⊥ ⊑ iterate f n ⊥.
    Proof.
        assert (forall n, iterate f n (bot D eqD R) ⊑ iterate f (S n) ⊥) as Ha.
        {
            induction n.
            -   apply bot_prop.
            -   apply monotonicity with (R2 := R) (f := f) in IHn.
                apply IHn.
                assumption.
        }
        intros n m Hlt.
        induction Hlt.
        -   reflexivity.
        -   now transitivity (iterate f m0 ⊥).
    Qed.

End A.  


 Section Continuous.

    Variable D1 : Type.
    Variable eqD1 : relation D1.
    Variable R1 : relation D1.
    Variable D2 : Type.
    Variable eqD2 : relation D2.
    Variable R2 : relation D2.

    (* Context `{EA1 : Equivalence D1 eqD1}. *)
    (* Context `{EA2 : Equivalence D2 eqD2}. *)

    Infix "⊑" := R1 (at level 80).
    Infix"≼" := R2 (at level 80).

    (* Context `{R1_PartialOrder : PartialOrder D1 eqD1 R1}. *)

    (* Context `{R2_PartialOrder : PartialOrder D2 eqD2 R2}. *)

    Context `{DCPO1 : DCPO D1 eqD1 R1}.
    Context `{DCPO2 : DCPO D2 eqD2 R2}.

    Notation "⊔1" := (lub D1 eqD1 R1).
    Notation "⊔2" := (lub D2 eqD2 R2).

    Class Continuous (f : D1 -> D2) :=
        continuity : forall (P : D1 -> Prop), 
            directed R1 P ->  f (⊔1 P) = ⊔2 (f @ P).


End Continuous. 

Section TestContinuous.
    Variable D1 D2 : Type.
    Variable eqD1 : relation D1.
    Variable eqD2 : relation D2.
    Variable R1 : relation D1.
    Variable R2 : relation D2.
    
    Variable f : D1 -> D2.

    (* Context `{DCPO1 : Equivalence D1 eqD1}. *)
    (* Context `{DCPO2 : Continuous D1 eqD1 R1 D2 eqD2 R2 f}. *)
    Context `{DCPO1 : CPO D1 eqD1 R1}.
    Context `{DCPO2 : CPO D2 eqD2 R2}.

    Definition c : D1.
    exact (bot D1 eqD1 R1).
    Defined.

    Context `{Cont : Continuous D1 eqD1 R1 D2 eqD2 R2 f}.
    
    Definition d : D1.
    exact (@bot D1 eqD1 R1 H3 H4 DCPO1).
    Defined.

End TestContinuous.

(**)
 Section Fixpoints.

    Variable D : Type.

    Variable eqD : relation D.

    Variable R : relation D.

    Infix "⊑" := R (at level 80).
    Infix"≼" := R (at level 80).

    (* Context `{EQD : Equivalence D eqD}.
    Context `{R_PartialOrder : PartialOrder D (@eq D) R}. *)

    Variable f : D -> D.

    Definition fixpoint (x : D) `{EQD : Equivalence D eqD} := eqD (f x) x.

    Definition prefixpoint (x : D) :=  f x ⊑ x.

    Definition postfixpoint (x : D) := x ⊑ f x.

End Fixpoints. 

Check fixpoint.

 
Section Kleene.

    Variable D : Type.
    Variable eqD : relation D.
    Variable f : D -> D.
  
    Variable R : relation D.

    Context `{Cpo : CPO D eqD R}. 

    Context `{Mo : Monotonic D R D R f}.
    
    Definition c : D.
        exact (bot D eqD R).
    Defined.

    Context `{continuousf : Continuous D eqD R D eqD R f}.

     Definition b : D.
        exact (bot D eqD R).

    Infix "⊑" := R (at level 80).
    Notation "⊥" := (bot D eqD R).


    (* CoInductive fn : D -> Prop :=
        fn_ : forall x n, x = iterate f n (bot D R) -> fn x.        *)

    Definition a : D.
    exact (bot D eqD R).


    Definition fn : D -> Prop := fun x => 
        exists n, x = iterate f n (bot D eqD R).

    (*  *)
    Lemma fn_chain : chain R fn.
    Proof.
        unfold chain.
        intros x y Ha Hb.
        destruct Ha as [n Ha].
        destruct Hb as [m Hb].
        subst.
        destruct (le_ge_dec n m).
        -   left.
            now apply iterate_prop.
        -   right.
            now apply iterate_prop.
    Qed.

    (* direction is preserved by monotonicity *)
    Lemma v : directed R (image f fn).
    Admitted.

    Lemma w : forall n, image f fn (iterate f (S n) (bot D R)).
    Admitted.

    Lemma u : eqD (lub D R (image f fn)) (lub D R fn).
    Proof.
        assert (directed R fn) by auto using fn_chain, chaindirected. 
        assert (forall x, (image f fn) x ->  x ⊑ lub D R fn).
        {
            intros x HIm.
            apply lub_prop1.
            assumption.
            destruct HIm as [y [[n Ha] Hb]]; subst.
            exists (S n); reflexivity.
        }
        assert (forall x, fn x -> x ⊑ lub D R (image f fn)).
        {
            intros x Hx.
            destruct Hx as [n Hx]; subst.
            destruct n.
            -   transitivity (iterate f 1 (bot D R)).
                +   apply iterate_prop; intuition.
                +   apply lub_prop1.
                    apply v.
                    exists (iterate f 0 (bot D R)).
                    split.
                    *   exists 0; reflexivity.
                    *   reflexivity.
            -   apply lub_prop1; auto using v,w.
        }
        apply antisymmetry.
        -   apply lub_prop2; auto using v.
        -   now apply lub_prop2.
Qed. 

    (* Proposition a : fixpoint D eqD f (@lub D R DCPO1 fn).
    Proof.
        assert (bot D R ⊑ f (bot D R)) by apply bot_prop.

        assert (directed R fn).
        now apply chaindirected.
        unfold fixpoint.
        replace (f (lub D R fn)) with (lub D R (image f fn)).
        Unset Printing All.

        admit.
        symmetry.
        unfold Continuous in *.
        generalize (continuousf fn H2). intro.
        apply H3.
    Qed. *)
End TestContinuous.
 (* pEnd Kleene. *) *)

