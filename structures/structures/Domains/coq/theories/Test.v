    Require Import Coq.Logic.Classical_Pred_Type.
    
    Definition partial (A B : Type) := A -> option B.

    Axiom A B: Type.
    Check (A -> B).
    Check (A -> option B).
    Axiom lub : option B -> option B -> option B -> Prop.
    Axiom elub : forall x y, exists z, lub x y z.  
    Definition ple0 (f : partial A B) (g : partial A B) : partial A B.
        intro x.
        generalize (elub (f x) (g x)).
        intro.
        destruct H.
        Admitted.

    Definition ple A B (f : partial A B) (g : partial A B) : Prop :=
        forall x, f x <> None -> g x <> None /\ f x = g x.

    (* dans un cpo, si on demande que le lub soit calculable alors les
    fonctions ne forment pas un dcpo car le leur lub ne l'est pas ??? *)
    (* en tout cas pas le lub d'une famille infini *)
    (* quid si les parties infinies sont des coinductifs *)
    (* problement on ne peut pas exprimer qu'un type est coinductif *)
    (* c'est pourquoi des solutions prenent des familles indexées (omega) *)

    (* si on prend des familles indexées, ou les éléments de base ont 
    un lub calculable. Peut on calculé le lub d'une famille indexée 
    de fonctions *)

    (* Plus généralement, si on a op : A -> A -> B *)
    (* peut on calculer le fold d'un stream -> 
        NON, seulement montrer l'existence *)
    (* on retombe encore sur un lub non calculable *)
    (* le lub doit être une propriété *)
    (* problème, dans (a) on doit exhiber une fonction et donc la construire *)
    (* il faudrait que la fonction soit elle même une relation *)
    (* pour calculer la fonction union, il faut calculer l'union 
    sur les images, or on sait qu'elle existe mais on ne sait 
    pas nécessairement la calculer. Donc h ne peut pas être une fonctoin *)
    Lemma a : forall A B (f : partial A B) (g : partial A B),
        exists h, ple A B f h /\ ple A B g h.
    Proof.
        intros.


    (* suite infinie d'éléments *)

    Definition nat_top := option nat.

    Definition ble (n m : nat_top) :=
        match (n,m) with 
                (_ , None) => True  
            |   (None, Some m) => False
            |   (Some n, Some m) => le n m 
        end. 
    
    (* easy because the bound does not depend on P *)
    Lemma u : forall (P : nat_top -> Prop), exists n, forall m, P m -> ble m n.
    Proof.
        intros.
        apply not_all_not_ex.
        intro.
        destruct (H None).
        intros.
        destruct m; unfold ble; exact I.
    Qed.

    Lemma v : forall (P : nat_top -> Prop), 
        exists n, (forall m, P m -> ble m n) /\ 
            forall o, (forall m, P m -> ble m o) -> ble n o.
    Proof.
        intros.
        apply not_all_not_ex.
        intro.
        destruct (H None).
        split.
        -   intros.
            destruct m; unfold ble; exact I.
        -   intros.
