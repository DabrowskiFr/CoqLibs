From Coq Require Import Setoid.
(* From mathcomp Require Import fintype. *)
(* Require Import mathcomp.ssreflect.seq. *)
(* Require Import mathcomp.ssreflect.tuple. *)
(* From reactive.streams Require Import stream. *)

Require Import Ensembles.
Require Import DecidableType.
Notation "a ∈ A" := (In _ A a) (at level 10).

Lemma a : forall A Γ Γ', Included A Γ (Union A Γ Γ').
Proof.
    unfold Included.
    intros.
    apply Union_introl.
    assumption.
Qed.
(* 
Lemma b : forall (A : Type) Γ f, f ∈ (Add A Γ f).
Proof.
    intros A Γ f.
    unfold Add.
    apply Union_intror.
    constructor.
Qed. *)

(* Formule pure sans environnement, éléments de base qui sont des valeurs de vérité 
    : propositions ? pas vraiment des variables moralement *)
(* logique proposition, prédicat (notion de terme) , premier ordre *)
(* type class pour interpretation *)

(* système logique ? *)
(* objet syntaxique, source de l'interprétation, interpretation *)
(* etant donné des formules comment appelle t on le domain d'interpretation *)

Require Import mathcomp.ssreflect.choice.
From mathcomp Require Import finmap.

Require Import FMapInterface.
Module FirstOrder.

    (* Variable V : finType.
    Variable F : finType.
    Variable P : finType.
    Variable f_arity : F -> nat.
    Variable p_arity : P -> nat. *)

    (* V : Type *) (* Module Decidable Type *)

    Declare Module V : DecidableType.
    Declare Module M : WS.

    (* Parameter V : countType. *)

    Record family (X : Type) := { 
        family_index :> Type; 
        family_element :> family_index -> X
    }.

    Arguments family_index [X].
    Arguments family_element [X _].

    Record signature : Type := {
        Sorts : Type;
        Funcs : family (list Sorts * Sorts);
        Preds : family (list Sorts)
    }.

    Notation ar F := (fst (family_element F)) (only parsing).
    Notation res F := (snd (family_element F)) (only parsing).
    Notation arP P := (family_element P) (only parsing).


    (** Heterogeneous lists from Adam Chlipala’s CPDT. *)

(** Heterogeneous lists from Adam Chlipala’s CPDT. *)

    (* Require Import List.
    Import ListNotations. *)

    Section HList.

      Context (J : Type) (A : J -> Type).

        Inductive HList : list J -> Type :=
        | HNil  : HList nil
        | HCons : forall j js, A j -> HList js -> HList (cons j js).
    
    End HList.

    (* tuples inspirés de HList *)

    Arguments HList {J} A w : rename.
    Arguments HNil {J A}.
    Arguments HCons {J A j js}.

    Open Scope fmap_scope.

    Section Term.

    Definition Ctx (Σ : signature) := M.t (Sorts Σ).

    Variables (Σ : signature) (Γ : Ctx Σ).

    Inductive Term  : Sorts Σ -> Type :=
        | T_Var : forall (x : M.E.t) (t : Sorts Σ), 
            M.find x Γ = Some t -> Term t
        | T_App : forall (F : Funcs Σ),
            HList Term (ar F) -> Term (res F).

    End Term.

    Record algebra (Σ : signature) : Type := {
        interp_sort : Sorts Σ -> Type;
        interp_f_symb (F : Funcs Σ) :
            HList interp_sort (ar F) -> interp_sort (res F);
        interp_p_symb (P : Preds Σ) : HList interp_sort (arP P)
    }.

    Definition a (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) 
        (x : M.E.t) (H : M.In x Γ) :  Sorts Σ.
    Proof.
        case_eq (M.find x Γ).
        -   intros.
            exact s.
        -   intros.
            exfalso.
            destruct H.
            apply M.find_1 in H.
            congruence.
    Defined.

    Definition env (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) : Type :=
        forall (x : M.E.t) (H : M.In x Γ), interp_sort Σ A (a Σ A Γ x H).

    Definition env' (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) : Type :=
        forall (x : M.E.t) (t : Sorts Σ) (H : M.find x Γ = Some t), interp_sort Σ A t.

    Lemma b : forall (Σ : signature) (x : M.E.t) (Γ : Ctx Σ) t, 
        (M.find x Γ = Some t) -> M.In x Γ.
    Admitted.

(* Require Import Coq.Program.Equality. *)

    

    (* Fixpoint interp_term (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) (σ : env' Σ A Γ)
        (ty : Sorts Σ) (t : Term Σ Γ ty) : interp_sort Σ A ty.
        refine (
        match t with 
            | T_Var x ty H => σ x ty H 
            | T_App f hl => 
                let l := 
                    (fix g hl := match hl with HNil => _ | HCons _ _ a0 l' => _  end) hl
                in interp_f_symb Σ A f l
        end
        ).
        induction hl.
        - exact HNil.
        - exact (HCons (interp_term Σ A Γ σ _ a0) IHhl).
Defined. *)

    Fixpoint interp_term' (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) (σ : env' Σ A Γ)
        (ty : Sorts Σ) (t : Term Σ Γ ty) : interp_sort Σ A ty.
        refine (
        match t with 
            | T_Var x ty H => σ x ty H 
            | T_App f hl => 
                let l := _
                in interp_f_symb Σ A f l
        end
        ).
        induction hl.
        - exact HNil.
        - apply HCons.
            eapply (interp_term' Σ A Γ σ).
            apply a0.
            apply IHhl.
        Qed.
        (* exact (HCons (interp_term Σ A Γ σ _ a0) IHhl).
Defined. *)

    (* map ?? *)
(*
    Fixpoint interp_term (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) (σ : env' Σ A Γ)
        (ty : Sorts Σ) (t : Term Σ Γ ty) : interp_sort Σ A ty.
        refine (
        match t with 
            | T_Var x ty H => σ x ty H 
            | T_App f hl => 
                let l := _ 
                in interp_f_symb Σ A f l
        end
        ).
        induction hl.
        - exact HNil.
        - exact (HCons (interp_term Σ A Γ σ _ a0) IHhl).
Defined.
Check HList_rect.
Print interp_term.
*)
    (* induction scheme for terms*)

    (* ou auxilliary function *)
(*
    Fixpoint interp_term'' (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) (σ : env' Σ A Γ)
        (ty : Sorts Σ) (t : Term Σ Γ ty) {struct t}: interp_sort Σ A ty :=
        match t in (Term _ _ s) return (interp_sort Σ A s) with 
            | T_Var x ty H => σ x ty H 
            | T_App f hl => interp_f_symb Σ A f (interp_terms Σ A Γ σ _ hl) 
        end 
        with interp_terms (Σ : signature) (A : algebra Σ) (Γ : Ctx Σ) (σ : env' Σ A Γ)
           k (l : HList (Term Σ Γ) k) {struct l} : HList (interp_sort Σ A) k :=
            match l with 
                | HNil => HNil 
                | HCons _ _ a0 l' => 
                    HCons (interp_term'' Σ A Γ σ _ a0) (interp_terms Σ A Γ σ _ l')
        end. 
Print interp_term.
*)
    (* Definition lift_ty [A B] (f : A -> B) x := (map f (fst x), f (snd x)). *)

    (* Record algebra (Σ : signature) : Type := {
        interp_sort : sort Σ -> Type;
        interp_f_symb (f : family_index (sort Σ)) : 
            unfold (List.map interp_sort (f_ar f)) (interp_sort (f_res f));
        interp_p_symb (p : p_symb Σ) :
            unfold (List.map interp_sort (p_ar p)) Prop
    }. *)

    (* app : nuplet de termes ayant la bonne sort *)
    (* à partir du nuplet de sort -> nuplet de terme de sort *)
    (* A1 * ... An -> term Sigma A1 .... An *)
    (* Inductive term (Σ : signature) (Γ : list (V * sort Σ)) : sort Σ -> Type := 
        | T_Var x : forall t, List.In (x, t) Γ -> term Σ Γ t
        | T_App : forall t (f : f_symb Σ) (n : nat),
            tuple_of n (term Σ Γ (sort Σ)) -> (* of_list *)
            (* map_tuple (term Σ Γ) n  ->  *)
            term Σ Γ t. *)

    (* tuple n Type -> Type *)

    Fixpoint unfold (l : list Type) (r : Type) :=
        match l with 
            | nil => r 
            | cons h t => h -> (unfold t r)
        end. 

    (* apply unfold *)


    (* Record algebra (Σ : signature) : Type := {
        interp_sort : sort Σ -> Type;
        interp_f_symb (f : f_symb Σ) : 
            unfold (List.map interp_sort (f_ar f)) (interp_sort (f_res f));
        interp_p_symb (p : p_symb Σ) :
            unfold (List.map interp_sort (p_ar p)) Prop
    }. *)

    (* symbol -> n, tuple n*)
    (* tuple n *)



    (* Fixpoint interp_term (Σ : signature) (A : algebra Σ) (σ : V -> sort Σ) 
        (t : term Σ) : sort Σ := (* sort -> unfold *)
        match t with 
            | T_Var x => σ x
            | T_App f l => 
                interp_f_symb Σ A f (* apply to the list *)
                (* ifun _ s f (List.map (interp_term s) l) *)
        end. *)
    (* Parameter v_eq_dec : forall x y:V, {x=y}+{x<>y}. *)
(*
    Inductive term : Type := 
        | T_Var : V -> term 
        | T_App : F -> list term -> term.

    Inductive formula : Type :=
        | F_App : P -> list term -> formula 
        | F_False : formula 
        | F_Imp : formula -> formula -> formula 
        | F_Forall : V -> formula -> formula 
        | F_Exists : V -> formula -> formula. 
*)
    (* signature, sorts, fun, pred *)
(*
    Record structure (univ : Type) : Type := Struct {
        ifun : F -> list univ -> univ; (*algebra : sort -> Type*)
        ipred : P -> list univ -> Prop; (* algebra *)
        ivar : V -> univ
    }.*)
(*
    Fixpoint interp_term {univ : Type} (s : structure univ) (t : term) : univ :=
        match t with 
            | T_Var x => ivar _ s x
            | T_App f l => ifun _ s f (List.map (interp_term s) l)
        end.

    Definition update {univ : Type} (s : structure univ) (x : V) (a : univ) : structure univ :=
        Struct _ (ifun _ s) (ipred _ s) 
            (fun y => if v_eq_dec y x then a else ivar _ s x).

    Fixpoint interp_form {univ : Type} (s : structure univ) (f : formula) : Prop :=
    match f with 
        | F_App p l => ipred _ s p (List.map (interp_term s) l)
        | F_False => False
        | F_Imp f g => ~ (interp_form s f) \/ (interp_form s g)
        | F_Forall x f => 
            forall y : univ, interp_form (update s x y) f
        | F_Exists x f =>
            exists y : univ, interp_form  (update s x y) f
    end.

    Inductive satisfiable (f : formula) : Prop :=
        satisfiable_ : forall u (s : structure u), 
            interp_form s f -> satisfiable f.
*)
    (* Inductive proof (Γ : Ensemble formula) (f : formula) : Prop := *)

End FirstOrder.

(*
Module Predicate.

    (* Predicate calculus or First order logic *)

    (* tuple (n) *)

    Variable V : finType.
    Variable F : finType.
    Variable C : finType.
    Variable P : finType.
    Variable f_arity : F -> nat.
    Variable p_arity : P -> nat.

    Inductive term : Type := 
        | T_Var : V -> term 
        | T_Cst : C -> term
        | T_App : F -> list term -> term.

    Inductive formula : Type :=
        | F_predicate : P -> list term -> formula 
        | F_Not : formula -> formula 
        | F_And : formula -> formula 
        | F_Or : formula -> formula 
        | F_Imp : formula -> formula 
        | F_Forall : V -> formula -> formula 
        | F_Exists : V -> formula -> formula. 

    Variable D : Type.
    Variable env : V -> D.
    Variable c_interp : C -> D.
    Variable f_interp : F -> list D -> D.
    Variable p_interp : P -> list D -> Prop.

    Fixpoint interp_term (t : term) : D :=
        match t with 
            | T_Var x => env x
            | T_Cst c => c_interp
            | T_App f l => f_interp f l 
        end. 
    (* Fixpoint interpretation (f : formula) : Prop :=
        match f with  *)

    (* valid term *)
    (* Inductive formula : Type :=  *)

End Predicate.
    Inductive ltl_formula : Type := 
        | F_Atom : A -> ltl_formula
        | F_Not : ltl_formula-> ltl_formula
        | F_And : ltl_formula -> ltl_formula -> ltl_formula
        | F_Or : ltl_formula -> ltl_formula -> ltl_formula 
        | F_Imp : ltl_formula -> ltl_formula -> ltl_formula
        | F_IIf : ltl_formula -> ltl_formula -> ltl_formula
        | F_Eventually : ltl_formula -> ltl_formula
        | F_Finally : ltl_formula -> ltl_formula 
        | F_Until : ltl_formula -> ltl_formula -> ltl_formula 
        | F_Next : ltl_formula -> ltl_formula .

    (* Fixpoint interpretation (f : formula) : stream A -> Prop  *)
*)
(* End Propositional. *)