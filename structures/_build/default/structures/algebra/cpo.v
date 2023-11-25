(* Relations *)

Definition relation (A : Set) := A -> A -> Prop.

Definition reflexive (A : Set) (R : relation A) := forall x : A, R x x.

Definition transitive (A : Set) (R : relation A) := forall x y z : A, R x y -> R y z -> R x z.

Definition asymetric (A : Set) (R : relation A) := forall x y : A, R x y -> R y x -> x = y.

Arguments reflexive [A] R.
Arguments transitive [A] R.
Arguments asymetric [A] R.


(* Partial orders *)

Record po (t : Set) (R : relation t) :=
  PO
    {
      po_reflexive : forall x, R x x;
      po_transitive : transitive R;
      po_asymetric : asymetric R;
    }.

Definition directed (A : Set) (R : relation A) (P : A -> Prop) :=
  forall x y : A, P x -> P y -> exists z, P z /\ R x z /\ R y z.

Definition chain (A : Set) (R : relation A) (P : A -> Prop) :=
  forall x y : A, P x -> P y -> R x y \/ R y x.

Lemma chain_directed : forall A R P, po A R -> chain A R P -> directed A R P.
Proof.
  intros A R P h_po h_chain.
  intros x y h_Px h_Py.
  destruct (h_chain x y h_Px h_Py).
  - exists y; destruct h_po; eauto.
  - exists x; destruct h_po; eauto.
Qed.

Definition lub (A : Set) (R : relation A) (P : A -> Prop) (a : A) :=
  (forall x, P x -> R x a) /\ (forall b, (forall x, P x -> R x b) -> R a b).

Lemma po_lub_unicity :
  forall (A : Set) (R : relation A) (PO : po A R) (P : A -> Prop) (a b : A),
    lub A R P a -> lub A R P b -> a = b.
Proof.
  intros A R PO P a b h_luba h_lubb.
  destruct h_luba.
  destruct h_lubb.
  apply H0 in H1.
  apply H2 in H.
  now apply (po_asymetric _ _ PO).
Qed.

Record dcpo (t : Set) (R : relation t):=
  DCPO
    {
      dcpo_reflexive : reflexive R;
      dcpo_transitive : transitive R;
      dcpo_asymetric : asymetric R;
      dcpo_lub : forall P, directed t R P -> exists a, lub t R P a
    }.

Record cpo (t : Set) (R : relation t) (bot : t):=
  CPO
    {
      cpo_reflexive : reflexive R;
      cpo_transitive : transitive R;
      cpo_asymetric : asymetric R;
      cpo_bot_inf : forall y, R bot y;
      cpo_lub : forall P, directed t R P -> exists a, lub t R P a
    }.

Lemma cpo_po : forall A R bot, cpo A R bot -> po A R.
Admitted.

(* Hint Resolve cpo_po. *)

(* Lemma cpo_lub_unicity :
  forall (A : Set) (R : relation A) (bot : A) (CPO : cpo A R bot) (P : A -> Prop) (a b : A),
    lub A R P a -> lub A R P b -> a = b.
Proof.
  eauto using po_lub_unicity.
Qed. *)
    
(* Highly non trivial *)
(* Lemma cpo_cond1 : forall (A : Set) (R : relation A),
    po A R -> (CPO A R <-> forall P, chain A R P -> exists a, lub A R P a).
Admitted.
*)
(* Functions *)

Definition monotonic t R bot t' R' bot' (S : cpo t R bot) (S' : cpo t' R' bot') (f : t -> t') :=
  forall x y, R x y -> R' (f x) (f y).

Definition image (A B : Set) (P : A -> Prop) (f : A -> B) : (B -> Prop) :=
  fun y => exists x, P x /\ f x = y.

Definition continuous t R bot t' R' bot' (S : cpo t R bot) (S' : cpo t' R' bot') (f : t -> t') :=
  forall P P' a b,
    monotonic t R bot t' R' bot' S S' f ->
    image t t' P f = P' ->
    lub t R P a ->
    lub t' R' P' b ->
    f a = b.

(* Fixpoints *)

Definition fp (A : Set) (f : A -> A) (a : A) : Prop :=
  f a = a.

Definition lfp t R bot (S : cpo t R bot) (f : t -> t) (a : t) : Prop :=
  fp t f a /\ forall b, fp t f b -> R a b.
(* 
Fixpoint iterate (S : cpo) (f : t S -> t S) (n : nat) ( x : t S):=
  match n with
    0 => x
  | S n => f (iterate S f n x)
  end. *)

(*
Lemma iterate_m : forall (C : cpo) (f : t C -> t C),
    monotonic C C f ->
    forall n : nat, (R C) (iterate C f n (bot C)) (iterate C f (S n) (bot C)).
Proof.
  intros S f h_monotonic n.
  induction n.
  - apply h_bot.
  - now apply h_monotonic.
Qed.
*)
(*
Lemma iterate_m2 :  forall (S : cpo) (f : t S -> t S),
    monotonic S S f ->
    forall n m : nat, n < m -> (R S) (iterate S f n (bot S)) (iterate S f m (bot S)).
Proof.
  intros.
  induction H0.
  - apply iterate_m.
    assumption.
  - set (A := h_po S).
    inversion A; subst.
Admitted.
    *)
    (*
Definition iter_bot (S : cpo) (f : t S -> t S) : t S -> Prop :=
  fun x => exists n, x = iterate S f n (bot S).

Lemma iter_chain : forall S f, (chain (t S) (R S) (iter_bot S f)).
Proof.
  unfold chain.
  intros S f x y h_iterx h_itery.
  destruct h_iterx as [n Ha].
  destruct h_itery as [m Hb].

  
  induction h_iterx; intros.
  - left.
    apply (h_bot S).
  - generalize (IHh_iterx y H); intro.
    induction H.
    + right.
      apply (h_bot S).
    + destruct IHh_iterx.
  intros.






Theorem Fix :
  forall (S : cpo) (f : t S -> t S) a,
    lub (t S) (R S) (iter S f) a ->
    continuous S S f -> lfp S f a.
Proof.
  intros S f a h_lub h_continuous.
  assert (R S (bot S) (f (bot S))) by apply (h_bot S).



(*  Lemma cpo_cond1 : forall (A : Set) (R : relation A),
    po A R -> (CPO A R <-> forall P, chain A R P -> exists a, lub A R P a).
Proof.
  intros A R H_po.
  split.
  - intros H_cpo P H_chain.
    destruct H_cpo as [_  [ _ Ha]].
    apply Ha.
    now apply chain_directed.
  - intros H_chain.
    split; [assumption | split].
    + assert (chain A R (fun x => False)) by admit.
      destruct (H_chain (fun x => False) H) as [bot H_bot].
      assert (forall a, forall x, (fun x => False) x -> R x a).
      {
        intros.
        elim H0.
      }
      destruct H_bot as [Ha Hb].      
      exists bot.
      intro y.
      apply Hb.
      apply (H0 y).
    + intros.
Admitted.*)
*)