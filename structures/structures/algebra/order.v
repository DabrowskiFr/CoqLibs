Definition set (A : Set) P := {x : A | P}.

Module Relt.

  (* On doit pouvoir considérer une définition, e.g .refl, sur une partie *)
  (* cas de l'égalité sur les fonctions/relations *)
  (* proof irrelevance*)

  Definition set (A : Type) := A -> Prop.
  
  (* A and B must be of kind Type if proposition are to be domains *)
  
  Definition relation (A B : Type) := A -> B -> Prop.

  Section Defs.

    Context {A : Type}.
    
    Class Reflexive (P : set A) (R : relation A A) :=
      reflexivity : forall x : A, P x -> R x x.
    
    Class Irreflexive (P : set A) (R : relation A A) :=
      irreflexivity : forall x : A, P x -> R x x.
    
    Class Transitive (P : set A) (R : relation A A) :=
      transitivity : forall x y z : A, P x -> P y -> P z -> R x y -> R y z -> R x z.
    
    Class Symmetric (P : set A) (R : relation A A) :=
      symmetry : forall x y : A, P x -> P y -> R x y -> R y x.

    Class Asymmetric (P : set A) (R : relation A A) :=
      asymmetry : forall x y : A, P x -> P y -> R x y -> R y x -> False.
    
   (* Class Equivalence (P : set A) (R : relation A A) :=
      {
        Equivalence_Reflexive :> Reflexive P R;
        Equivalence_Transitive :> Transitive P R;
        Equivalence_Symmetric: > Symmetric P R
      }.

    Class Antisymmetric (P : set A) Eq `(H : Equivalence P Eq)(R : relation A A) :=
      antisymmetry : forall x y : A, P x -> P y -> R x y -> R y x -> Eq x y.
*)
    (* Class PartialOrder (P : set A) Eq `(H : Equivalence P Eq) (R : relation A A) := 
      {
        PartialOrder_Reflexive :> Reflexive P R;
        PartialOrder_Transitive :> Transitive P R;
        PartialOrder_Antisymmetric :> Antisymmetric Eq H P R
      }. *)

    Definition inclusion (A : Type) : relation (set A) (set A):=
      fun P Q => forall x, P x -> Q x.

  End Defs.

  (* Hint Unfold inclusion. *)
  
  Instance inclusion_Reflexive (A : Set) (P : set (set A)) : Reflexive P (inclusion A).
  Proof.
  Admitted.

  Instance inclusion_Transitive (A : Set) (P : set (set A)) : Transitive P (inclusion A).
  Admitted.
  
  Axiom ext : forall (A : Type) (P Q : set A),  (forall x, (P x <-> Q x)) -> P = Q.
  
  Hint Resolve ext : ext.
  End Relt.
  (* Instance inclusion_Antisymmetric (A : Set) (P : set (set A)) : Antisymmetric P (inclusion A).
  Proof.
    intros x y Hx Hy Ha Hb.
    apply ext; intuition.
  Qed. *)

  (* Instance inclusion_PartialOrder (A : Set) (P : set (set A)) : PartialOrder P (inclusion A). 
  Proof.
    constructor.
    apply inclusion_Reflexive.
    apply inclusion_Transitive.
    apply inclusion_Antisymmetric.
  Qed. *)

  
    
  (* ordre sur les ensembles *)
  (* inclusion *)
  
  
  (* Hint Unfold reflexive transitive antisymmetric. *)

  (*
  Lemma reflexive_inclusion :
    forall A P, reflexive (set A) (P : set (set A)) (inclusion A). 
  Proof.
    auto.
  Qed.
  
  Lemma transitive_inclusion :
    forall A P, transitive (set A) (P : set (set A)) (inclusion A). 
  Proof.
    auto.
  Qed.

  
  Lemma antisymmetric_inclusion :
    forall A P, antisymmetric (set A) (P : set (set A)) (inclusion A). 
  Proof.
  
  Qed.

  Definition po (A : Type) (P : set A) (R : relation A A) :=
    reflexive A P R /\  transitive A P R /\ antisymmetric A P R.
  
  Definition dpo (A : Type) (P : set A) (R : relation A A) :=
    reflexive A P R /\  transitive A P R /\ antisymmetric A P R /\
    forall x y : A, P x -> P y -> exists m, P m /\ R x m /\ R y m.

  Definition cpo (A : Type) ( P : set A) (R : relation A A) :=
    reflexive A P R /\  transitive A P R /\ antisymmetric A P R /\
    forall Q : set A,  inclusion _ Q P -> exists m, forall z, Q z -> R z m.

  Definition lub (A : Type) (P : set A) (R : relation A A) (H : po A P R) (x : A) :=
    forall y : A, P y -> R y x. 

  
End Relt.

Module RPair.
  
  Definition relation (A B : Set) := A -> B -> Prop.
  
  Definition reflexive (A : Set) (P : Prop) (R : relation A A) :=
    forall x : {x : A | P}, R (proj1_sig x) (proj1_sig x).
  
End RPair.

Module RAll.
  
  Definition relation (A B : Set) P Q m:= {x : A | P} -> {x : B | Q} -> Prop.
  
  Definition reflexive (A : Set) (P : Prop) (R : relation A A P P) :=
    forall x : {x : A | P}, R x x.
  
End RAll.
*)

