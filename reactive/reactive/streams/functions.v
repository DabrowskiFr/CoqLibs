From reactive.streams Require Import stream.

(* productivity, causality *)
(* causality : there exists a function, such that each prefix of the
result can be obtain by a prefix of the input *)
(* si deux fonctions même prefixe resultat alors même valeur *)
(* même préfixes -> égalité ??? bisimilarité *)

Open Scope stream_scope.

Inductive prefix {A : Type} : list A -> stream A -> Prop := 
| prefix_empty : forall s, prefix nil s
| prefix_cons : forall x l s,
    prefix l s ->
    prefix (cons x l) (str x s).

Definition lift {A : Type} (P : list A -> Prop) : stream A -> Prop :=
    fun s => forall l, prefix l s -> P l.

Lemma same_prefixes_eq_str : 
    forall A (s₁ s₂ : stream A), 
        (forall l, prefix l s₁ -> prefix l s₂) -> s₁ ∼ s₂.
Proof.
    cofix H.
    intros A [a s1] [b s2] H_prefix.
    constructor.
    -   assert (prefix (cons a nil) (b ⋅ s2)) as Hb.
        {
            assert (prefix (cons a nil) (a ⋅ s1)) as Ha 
                by do 2 constructor.
            exact (H_prefix _ Ha).
        } 
        replace b with a by (inversion Hb; congruence).
        reflexivity.
    -   assert (forall l : list A, prefix l (s1) -> prefix l (s2)) as Ha.
            {
                intros l Ha.
                assert (prefix (cons a l) (b ⋅ s2)) as Hc.
                {
                    assert (prefix (cons a l) (a ⋅ s1)) as Hb
                        by (constructor; exact Ha).
                    exact (H_prefix _ Hb).
                }
                inversion Hc as [ | ? ? ? Hd ]; subst.
                exact Hd.
            }
            exact (H _ _ _ Ha). 
Qed.    

Lemma bisimilar_same_eq_str : 
    forall A (s₁ s₂ : stream A),
        s₁ ∼ s₂ -> (forall l, prefix l s₁ -> prefix l s₂).
Proof.
    intros A s1 s2 H_bsim l.
    revert s1 s2 H_bsim.
    induction l; intros s1 s2 H_bsim H_prefix.
    -   constructor.
    -   destruct s1 as [a0 s1], s2 as [b s2].
        assert (a = b /\ prefix l s2) as [Ha Hb].
        {
            assert (a = a0 /\ prefix l s1) as [Ha Hb]
                by (inversion H_prefix; easy).
            assert (a0 = b /\ s1 ∼ s2) as [Hc Hd]
                by (inversion H_bsim; easy).
            replace b with a by congruence.
            firstorder (exact (IHl _ _ Hd Hb)).
        }
        replace b with a; now constructor.
Qed.




(* un flux est la limite de ces préfixes : conséquences *)
(* equiv until n-th *)

(* forme de déterminisme *)
(* Definition causal {A} (f : stream A -> stream A) :=
    forall (s1 s2 : stream A) (l : list A),
        prefix l s1 -> prefix l s2 ->   *)