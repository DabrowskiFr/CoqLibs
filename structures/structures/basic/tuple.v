
Inductive tuple (T : Type) : nat -> Type :=
| tuple_Z : tuple T 0
| tuple_S : forall  n (k : T) (t : tuple T n) , tuple T (S n). 

Definition first {n : nat} (t : tuple Type (S n)) : Type.
    inversion t.
    exact k.
Defined.

Print first.

Definition second {n : nat} (t : tuple Type (S n)) : tuple Type n.
    inversion t.
    exact t0.
Defined.

        (* pair A B -> prodn (A1 ... An) *)

        (* replace tuple with list ... *)

        (* Inductive prodn : forall n, (tuple Type n) -> Type :=
            | prodn_Z : prodn 0 (tuple_Z Type)
            | prodn_S : forall n (t : tuple Type (S n))
                (a : first t) (t' : prodn n (second t)),
                prodn n (second t)
        .         *)

    Require Import List.

        Inductive prodn : forall n, list Type -> Type :=
            | prodn_Z : prodn 0 List.nil
            | prodn_S {n : nat} {t : Type} {l : list Type} :
                t -> prodn n l -> prodn (S n) (List.cons t l).

        Definition prod (A B : Type) := prodn 2 (cons A (cons B nil)).

        Definition pair {A B : Type} (a : A) (b : B) : prod A B :=
            prodn_S a (prodn_S b prodn_Z).

        (* la liste de type n'est pas forcée d'avoir la bonne taille dans le type *)
        (* Definition prod (A B : Type) := prodn 3 (cons A (cons B nil)). *)


        Module Tuple.

        (* in mathcomp, sequence (list) the size of which is contrained *)
        (* here, the sequence has its size in its type*)

        (* same as finite list *)
        (* version with A1 A2 . A3 A4 -> more than one representation *)

     (*   Inductive tuple (T : Type) : nat -> Type :=
            | tuple_Z : tuple T 0
            | tuple_S { n : nat} : T -> tuple T n -> tuple T (S n). 
Print IDProp.
        Definition hd_t (T : Type) (n : nat) (t : tuple T (S n)) : T :=
            match t with 
                | tuple_Z => IDProp 
                | tuple_S _ t0 _ => t0 
            end.


        Definition tl_t (T : Type) (n : nat) (t : tuple T (S n)) : tuple T n :=
            match t with 
                |tuple_Z => IDProp 
                |tuple_S _ _ t1 => t1
            end.

        Print tl_t.

        Fixpoint map {T : Type} {n : nat} 
            (f : T -> T) (t : tuple T n) : tuple T n :=
                match t with
                    | tuple_Z => tuple_Z T
                    | tuple_S _ t ts => tuple_S _ (f t) (map f ts)
                end.

    (* version non induction de prodn *)
    (* prodn_ *)

        (* instantiate tuple type by Type *)
        Inductive prodn : forall {n}, tuple Type n -> Type :=
            | prodn_Z : prodn (tuple_Z Type)
            | prodn_S {n : nat} {T : Type} {t : tuple Type n} :
                T -> prodn t -> prodn (tuple_S Type T t).

                    (* prodn t -> tuple ... *)
                    
*)
(* Require Import Coq.Program.Equality. *)
        (*
        Definition hd (n : nat) (t : tuple Type (S n)) (p : prodn t) : hd_t _ _ t.
        dependent destruction t.
        simpl.
        inversion p; subst.
        exact X.
        Defined.

        Definition tl (n : nat) (t : tuple Type (S n)) (p : prodn t) : prodn (tl_t _ _ t).
        dependent destruction t.
        simpl.
        dependent destruction p.
        exact p.
        Defined.

        Print tl.

        (* Arguments prodn [n]. *)

        Definition prod (A B : Type) := 
            prodn (tuple_S Type A (tuple_S Type B (tuple_Z Type))).

        (* pair n'est pas le seul moyen de construire un produit ...*)
        (* il faut utiiser prodn_S *)
        Definition pair {A B : Type} (a : A) (b : B) : prod A B :=
            prodn_S a (prodn_S b prodn_Z).

        Definition first {A B : Type} ( x : prod A B) : A.
        inversion x; subst.
        exact X.
        Defined.

        Definition second {A B : Type} ( x : prod A B) : B.
        unfold prod in x.
        dependent destruction x.
        dependent destruction x.
        exact t1.
        Defined.

        Lemma a : forall A B x, @pair A B (first x) (second x) = x.
        Proof.
            intros.
            unfold pair.
            unfold prod in x.
            dependent destruction x.
            dependent destruction x.
            
        Admitted.
        (* Definition m (A B : Type) (F : Type -> Type) (f : A -> F A)
            p  *)

 Fixpoint tuple_of (l : list Type) : tuple Type (length l) :=
            match l as m return length l = length m -> tuple Type (length l) with 
                | nil => fun H => eq_rect_r _ (tuple_Z Type) H
                | cons t l => fun H => eq_rect_r _ (tuple_S Type t (tuple_of l)) H
            end (eq_refl (length l)). 


        Check (nat : Type).
        
        Definition a := tuple_of (cons (nat : Type) (cons (bool : Type) (cons (nat : Type) nil))).
        
        Compute a.

        End Tuple.

        (* Notation for tuples *)

        (* fonction liste de sortes l *)
        (* interprété par une fonction qui prend un prodn (map interp sort) l*)

(*    Definition fmap {n : nat} (f : Type -> Type) (T : Type) (n : nat) : Type :=
        tuple (f T) n. *)

    (* Inductive toto (Σ : signature): Type :=
        toto_ : forall t : sort Σ, toto Σ (term Σ t). *)

        Definition f1 (A : Type) (x : A) : A := x.
        (* prod Type Type : Type / prod Type Type != Type *)
        (* Definition f2 (A : prod Type Type) (a : A) := A. *)

        Definition g (f : Type -> Type) (A : Type * Type) : Type := 
            f (fst A) * f (snd A).

    (* Type * Type : pair de type *)
    (* prod Type Type : type *)



    Fixpoint trans (f : Type -> Type) (n : nat) (t : tuple Type n) : Type := 
        match t with 
            | tuple_Z => tuple_Z 
            | tuple_S n k t => tuple  (S n)
        end.

        *)
        End Tuple.