
From mathcomp Require Import fintype.
From reactive.streams Require Import stream.
Require Import Setoid.
(* interpretation proposition A -> Prop*)
(* interpretation ltl stream A -> Prop *)

    (* map elements of A to truth values *)

    (* states : mapping of variables *)

    (* computate : sequence of set of propositions *)

    (* Definition state (A : finType) := proposition A -> Prop. *)

    (* We map every possible execution to a computation by mapping each 
        configuration to the set of atomic propositions it satisfies *)
    (* Definition computation (A : finType) := stream (state A). *)
    (* or abstract A and map A to state B *)

    (* execution : sequence of configuration *)
    (* A computation is executable if there is an execution mapped to it *)

    (* notion d'etat *)
    (* les propositions parlent de ces états *)
    (* un calcul associe point à point à une suite d'état l'ensemble des 
        formules vérifiées *)
    (* ltl formulas over states *)
    (* formula syntax -> (state -> Prop) interpretation/mapping     *)

    (* models      
        valuation |- formula 
        computation |- temportal formula 
        *)

    (* semantics of a formula : state -> Prop *)



Module LTL.


    Definition formula (A : Set) := stream A -> Prop.

    Definition valid {A : Set} (P : formula A) := forall s, P s.

    Section Basics.

    Definition immediate {A : Set} (P : A -> Prop) : formula A :=
        fun s => P (hd s).

    (* Basic formulae *)

    (* propositions are a finite set of atomic propositions based 
        on a finite set of *)
    (* define LTL formula as an inductive type, syntax *)
    (* ltl formula in term of positions *)
    (* Form A = formules with variables x,..., in A*)
    (* Form A = formulas based on atomic propositions*)


    Inductive ttrue {A : Set} : formula A :=
        I : forall (s: stream A), ttrue s.
    
    Inductive tfalse {A} : formula A := .

    Definition notS {A : Set} (P : formula A) : formula A := 
        fun s => P s -> False.

    Definition or {A : Set} (P Q : formula A) : formula A :=
        fun s => P s \/ Q s.

    (* P must hold in the next state *)
    Definition next {A : Set} (P : formula A)  : formula A :=
        fun s => P (tl s).

    (* P must hold in all state until Q is satisfied in a state 
        (not included), Q must hold at some time *)
    Inductive until {A : Set} (P Q : formula A) : formula A :=
        | until_cur : forall s, Q s -> until P Q s 
        | until_cons : forall s, P s -> until P Q (tl s) -> until P Q s.

    End Basics.

Section Extended.

(* Extended formulae  *)

    Definition imp {A : Set} (P Q : formula A) : formula A := 
        fun s => P s -> Q s.

    Definition and {A : Set} (P Q : formula A) : formula A :=
        fun s => P s /\ Q s.

    Definition iff {A : Set} (P Q : formula A) : formula A :=
        and (imp P Q) (imp Q P).

    (* P must hold in a future state *)
    Definition finally {A : Set} (P : formula A) : formula A :=
        until ttrue P.

    (* P must hold until Q holds, if Q never holds P must always hold *)
    Definition release {A : Set} (P Q : formula A) : formula A :=
        notS (until (notS P) (notS Q)).

    (* P must hold in all states *)
    Definition globally {A : Set} (P : formula A) : formula A :=
        release tfalse P.

End Extended.
(* 
CoFixpoint ab : stream bool :=
    {|hd := false; tl := {| hd:= true; tl := ab|}|}.

CoFixpoint ba : stream bool :=
    {|hd := true; tl := {| hd := false; tl := ba|}|}.

Axiom seq : forall {A : Set} (s : stream A), 
    s = {| hd := hd s; tl := tl s|}.

Lemma hd1 : forall {A : Set} (a : A) (b : stream A) , 
    hd {| hd := a; tl := b|} = a.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Definition unrollStream {A :Set} (s : stream A) : stream A :=
    match s with 
        {| hd := a; tl := b|} => {| hd := a; tl := b |}
    end.
Lemma unrollStreamEq {A : Set} : 
    forall (s : stream A), s = unrollStream s.
Proof.
    intro.
    rewrite (seq s) at 1.
    reflexivity.
Qed.

Lemma hda : hd ab = false.
Proof.
    reflexivity.
Qed.

Definition current {A : Set} (P : A -> Prop) : formula A :=
    fun s => P (hd s).

(* notS tfalse <-> ttrue *)
(* false -> false <-> ttrue *)

*)

Definition equiv {A : Set} (P Q : formula A) : Prop := 
    (forall s, P s -> Q s) /\ (forall s, Q s -> P s).

Lemma equiv_refl {A : Set} :
    forall (P : formula A), equiv P P.
Proof.
    split; auto.
Qed.

Lemma equiv_trans {A : Set} :
    forall (P Q R : formula A),
        equiv P Q -> equiv Q R -> equiv P R.
Proof.
    intros.
    destruct H, H0.
    split; auto.
Qed.

Lemma equiv_sym {A : Set} :
    forall (P Q : formula A), equiv P Q -> equiv Q P.
Proof.
    intros.
    destruct H.
    split; auto.
Qed.

Add Parametric Relation A : (formula A) (@equiv A) 
    reflexivity proved by (equiv_refl (A:=A))
    symmetry proved by (equiv_sym (A:=A))
    transitivity proved by (equiv_trans (A:=A)) 
    as equiv_rel. 

Lemma notS_compat : forall {A : Set} (P P' : formula A),
    equiv P P' -> equiv (notS P) (notS P').
Proof.
    intros A P P' [Ha Hb].
    unfold notS.
    split.
    -   intros s H1 H2.
        exact (H1 (Hb s H2)).
    -   intros s H1 H2.
        exact (H1 (Ha s H2)).
Qed.

Add Parametric Morphism A : (@notS A)
    with signature (@equiv A) ==> (@equiv A) as notS_mor.
Proof.
    exact (@notS_compat A).
Qed.

Lemma or_compat : forall {A : Set} (P P' : formula A),
equiv P P' -> forall (Q Q' : formula A), equiv Q Q' -> equiv (or P Q) (or P' Q').
Proof.
    intros A P P' [Ha Hb] Q Q' [Hc Hd].
    unfold or.
    split.
    -   intros s [H1 | H2].
        +   left; exact (Ha _ H1).
        +   right; exact (Hc _ H2).
    -   intros s [H1 | H2].
        +   left; exact (Hb _ H1).
        +   right; exact (Hd _ H2).
Qed.

Add Parametric Morphism A : (@or A)
    with signature (@equiv A) ==> (@equiv A) ==> (@equiv A) as or_mor.
Proof.
    exact (@or_compat A).
Qed.
    
Lemma next_compat : forall {A : Set} (P P' : formula A),
    equiv P P' -> equiv (next P) (next P').
Proof.
    intros A P P' [Ha Hb].
    unfold next; split; auto.
Qed.

Add Parametric Morphism A : (@next A) 
    with signature (@equiv A) ==> (@equiv A) as next_mor.
Proof.
    exact (@next_compat A).
Qed.

Lemma until_compat : forall {A : Set} (P P' : formula A),
    equiv P P' -> forall (Q Q' : formula A), 
    equiv Q Q' -> equiv (until P Q) (until P' Q').
Proof.
    intros A P P' [Ha Hb] Q Q' [Hc Hd].
    split.
    -   fix HInd 2.
        intros s HUntil.
        inversion HUntil as [? HQs | ? HPs Htl]; subst.
        +   constructor 1.
            exact (Hc _ HQs).
        +   constructor 2.
            exact (Ha _ HPs).
            exact (HInd _ Htl).
    -   fix HInd 2.
        intros s HUntil.
        inversion HUntil as [? HQs | ? HPs Htl]; subst.
        +   constructor 1.
            exact (Hd _ HQs).
        +   constructor 2.
            exact (Hb _ HPs).
            exact (HInd _ Htl).
Qed.

Add Parametric Morphism A : (@until A)
    with signature (@equiv A) ==> (@equiv A) ==> (@equiv A) as until_mor.
Proof.
    exact (@until_compat A).
Qed.

Lemma finally_compat : forall {A : Set} (P P' : formula A),
    equiv P P' -> equiv (finally P) (finally P').
Proof.
    unfold finally; intros A P P' H.
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism A : (@finally A)
    with signature (@equiv A) ==> (@equiv A) as finally_mor.
Proof.
    exact (@finally_compat A).
Qed.

Lemma release_compat : forall {A : Set} (P P': formula A),
    equiv P P' -> forall (Q Q' : formula A), equiv Q Q' ->
    equiv (release P Q) (release P' Q').
Proof.
    unfold release.
    intros A P P' HP Q Q' HQ.
    rewrite HP, HQ; reflexivity.
Qed.

Add Parametric Morphism A : (@release A)
    with signature (@equiv A) ==> (@equiv A) ==> (@equiv A) as release_mor.
Proof.
    exact (@release_compat A).
Qed.

Lemma globally_compat : forall {A : Set} (P P' : formula A),
    equiv P P' -> equiv (globally P) (globally P').
Proof.
    unfold globally.
    intros A P P' HP.
    rewrite HP; reflexivity.
Qed.

Lemma untilS : forall {A : Set} (P Q : formula A),
    forall s, until P Q s -> Q s \/ (P s /\ until P Q (tl s)).
Proof.
    intros.
    inversion H; subst.
    left; apply H0.
    right.
    split.
    apply H0.
    apply H1.
    Qed.

Lemma notSProp : forall {A : Set},
    @equiv A (notS tfalse) ttrue.
Proof.
    intros.
    split.
    -   intros. 
        exact (I s).
    -   unfold notS; intros.
        inversion H0.
Qed.

(* redefinir globally coinductivement *)

Lemma valid_true : forall {A : Set}, @valid A ttrue.
Proof.
    unfold valid; intros.
    exact (I s).
Qed.

Lemma notS_imp : forall {A : Set} (P Q : formula A),
    valid (imp P Q) -> valid (imp (notS Q) (notS P)).
Proof.
    unfold valid, imp, notS.
    auto.
Qed.

Lemma or_left : forall {A : Set} (P Q : formula A), 
    valid (imp P (or P Q)).
Proof.
    unfold valid, imp, or; auto.
Qed.

Lemma next_imp : forall {A : Set} (P Q : formula A),
    valid (imp P Q) -> valid (imp (next P) (next Q)).
Proof.
    unfold valid, next, imp.
    auto.
Qed.

Lemma until_imp : forall {A : Set} (P P' : formula A),
    valid (imp P P') ->
    forall (Q Q' : formula A),
    valid (imp Q Q') ->
    valid (imp (until P Q) (until P' Q')).
Proof.
    unfold valid, imp.
    intros.
    induction H1; subst.
    -   constructor 1.
        auto.
    -   constructor 2.
        auto.
        assumption.
Qed.

Lemma imp_id : forall {A : Set} (P : formula A),
    valid (imp P P).
Proof.
    intros.
    unfold valid, imp.
    trivial.
Qed.

Lemma release_imp : forall {A : Set} (P P': formula A),
    valid (imp P P') -> forall (Q Q' : formula A), valid (imp Q Q') ->
    valid (imp (release P Q) (release P' Q')).
Proof.
    unfold release; auto using notS_imp, until_imp.
Qed.

Lemma globally_imp : 
forall {A : Set} (P Q : formula A),
    valid (imp P Q) ->
    valid (imp (globally P) (globally Q)).
Proof.
    unfold globally; auto using release_imp, imp_id.
Qed.



Lemma globally1 : forall {A : Set} (P Q : formula A),
    forall s, globally P s -> globally (or P Q) s.
Proof.
    intros.
    apply globally_imp with (P := P).
    apply or_left.
    apply H.
Qed.


Lemma untildist : forall {A : Set} (P Q R : formula A),
    equiv (until P (or Q R)) (or (until P Q) (until P R)).
Proof. (* can't use cofix, not coinductive result *)
    intros A P Q R; unfold or.
    split.
    -   intros s H.
        inversion H; subst.
        +   destruct H0.
            *   left.
                constructor 1.
                assumption.
            *   right.
                constructor 1.
                assumption.
        +
    Admitted.   



Lemma globally_idem : 
    forall {A : Set} (f : formula A), equiv (globally f) (globally (globally f)).
Proof.
    intros A f.
    unfold globally.
    split.
    -   intros s H.
Admitted.

            (* need an hypothesis on (tl s) *)

(* si conclusion predicat inductif -> cofix *)
(* sinon bisimulation *)

(* infinité de zéros *)
(* Lemma abProp1 : globally (finally (current (@eq _ false))) ab.
Proof.
    intro.
    assert (@equiv bool (notS tfalse) ttrue).
    apply notSProp.
    
Admitted.

Lemma abProp : globally (imp (current (@eq _ false)) (next (current (@eq _ true)))) ab.
Proof.
Admitted. *)

End LTL.

(*    Notation " p ∧ q " := ( ¬ p ⟶ q)(at level 7, right associativity).
    Notation " p ∨ q " := (¬(p ⟶ ¬ q))(at level 6, right associativity). 
    Notation " p ⟷ q " := ((p ⟶ q) ∨ (q ⟶ p))(at level 9, right associativity).   
*)

    (* Definition judgment := Ensemble formula * formula.

    Inductive rule : judgment -> Prop :=
        | ID : forall Γ (p : formula), p ∈ Γ -> Γ ⊢ p
        | MP : forall Γ (p q : formula), Γ ⊢ p -> Γ ⊢ p ⟶ q -> Γ ⊢ q
    where " Γ ⊢ p " := (rule (Γ, p)). *)