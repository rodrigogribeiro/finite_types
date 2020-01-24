Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Finite.Constructions.Vector
        Finite.Constructions.Cardinality
        Tactics.Tactics.

Import ListNotations.

Section Fixedpoints.
  Variable A : Type.
  Variable f : A -> A.

  Definition fp x := f x = x.

  Lemma fp_trans x : fp x -> fp (f x).
  Proof.
    congruence.
  Qed.
  
  Lemma fInduction
        (p : A -> Prop)
        (x : A)
        (px : p x)
        (IHf : forall y, p y -> p (f y)) n
    : p (Nat.iter n f x).
  Proof.
    induction n ; crush.
  Qed.

  Lemma fp_iter_trans x n
    : fp (Nat.iter n f x) -> forall m, m >= n -> fp (Nat.iter m f x).
  Proof.
    intros F m H. induction m.
    -
      destruct n ; crush.
    -
      decide (S m = n).
      +
        now rewrite e.
      +
        assert (m >= n) as G by omega.
        specialize (IHm G).
        simpl.
        now apply fp_trans.
  Qed.
End Fixedpoints.

Definition admissible (A : discType) f
  := forall xs : list A,  fp f xs \/ card (f xs) > card xs.

Lemma fp_card_admissible
      (A : discType) f n
  : admissible f ->
    forall xs : list A, fp f (Nat.iter n f xs) \/ card (Nat.iter n f xs) >= n.
 Proof.
   intros M xs. induction n.
     - cbn in *. right. omega.
     - simpl in *. destruct IHn as [IHn | IHn] .
       + left.  now apply fp_trans.
       + destruct (M ((Nat.iter n f xs))) as [M' | M'].
         * left.  now apply fp_trans.
         * right. omega. 
 Qed.

 Lemma fp_admissible (A : finType) (f : list A -> list A)
   : admissible f -> forall (xs : list A), fp f (Nat.iter (Cardinality A) f xs).
 Proof.
   intros F xs.
   destruct (fp_card_admissible (Cardinality A) F xs) as [H | H].
   -
     exact H.
   -
     specialize (F (Nat.iter (Cardinality A) f xs)).  destruct F as [F |F] ; crush.
     +
       pose proof (card_upper_bound (f (Nat.iter (Cardinality A) f xs))) ; crush.
Qed. 

Section FiniteIteration.
  Variable A : finType.
  Variable step : list A -> A -> Prop.
  Variable step_dec: forall xs x, dec (step xs x).

  Lemma pick xs : {x | step xs x /\ ~ (x el xs)} + forall x, step xs x -> x el xs.
  Proof.
    decide (forall x : A, step xs x -> x el xs).
    - tauto.
    - left. destruct (DM_notAll _ (p:= fun x => step xs x -> x el xs)) as [H _].
      destruct (finType_cc _ (H n)) as [x H']. firstorder.
  Defined.

  Definition finite_iter_step xs :=
    match (pick xs) with
    | inl L => match L with
                exist _ x _ => x :: xs end
    | inr _ => xs
    end.

  Definition finite_iter := Nat.iter (Cardinality A) finite_iter_step.

  Lemma finite_iter_step_admissible: admissible finite_iter_step.
  Proof.
    intro xs.
    unfold fp.
    unfold finite_iter_step.
    destruct (pick xs) as [[y [S ne]] | S] ; repeat (crush ; dec).
  Qed.

  Lemma finite_iter_fp xs : fp finite_iter_step (finite_iter xs).
  Proof.
    unfold finite_iter.
    apply fp_admissible.
    exact finite_iter_step_admissible.
  Qed.        

  (* inclp A p means every x in A satisfies p *)

  Lemma finite_iter_ind (p : A -> Prop) xs
    :  inclp xs p -> (forall xs x , (inclp xs p) -> (step xs x -> p x)) ->
       inclp (finite_iter xs) p.
  Proof.
    intros incl H. unfold finite_iter. apply fInduction.
    -
      assumption.
    -
      intros B H1 x E.
      unfold finite_iter_step in E.
      destruct (pick B) as [[y [S nE]] | S].
      +
        destruct E as [E|E] ; try subst x ; eauto.
      +
        auto.
  Qed. 

  Lemma list_cycle (B : Type) (xs : list B) x
    : x :: xs <> xs.
  Proof.
    intros D.
    assert (C : |x :: xs| <> |xs|) by (simpl; omega).
    apply C. now rewrite D.
  Qed.
  
  Lemma closure x xs : fp finite_iter_step xs -> step xs x -> x el xs.
  Proof.
    intros F.
    unfold fp in F.
    unfold finite_iter_step in F.
    destruct (pick xs) as [[y _] | S].
    -
      contradiction (list_cycle F).
    - exact (S x).
  Qed.

  Lemma closure_finite_iter x xs
    : step (finite_iter xs) x -> x el (finite_iter xs).
  Proof.
    apply closure.
    apply finite_iter_fp.
  Qed.

  Lemma preservation_step xs : xs <<= finite_iter_step xs.
  Proof.
    intro H.
    unfold finite_iter_step.
    destruct (pick xs) as [[y [S ne]] | S]; cbn; tauto.
  Qed.

  Lemma preservation_iter xs n
    : xs <<= Nat.iter n finite_iter_step xs.
  Proof.
    intros x E. induction n.
    -
      assumption.
    -
      simpl. now apply preservation_step.
  Qed.

  Lemma preservation_finite_iter xs : xs <<= finite_iter xs. 
  Proof.
    apply preservation_iter.
  Qed.

  Definition least_fp_containing f (ys xs : list A) :=
    fp f ys /\ xs <<= ys /\ forall ys', fp f ys' /\ xs <<= ys' -> ys <<= ys'.

  Definition step_consistent :=
    forall xs x, step xs x -> forall xs', xs <<= xs' -> step xs' x.

  Lemma step_iter_consistent
    : step_consistent -> forall xs x n, step xs x -> step (Nat.iter n finite_iter_step xs) x.
  Proof.
    intros H xs x n S. eapply H.
    -
      exact S.
    -
      apply preservation_iter.
  Qed.

  Lemma step_trans_fp_incl
    : step_consistent ->
      forall xs ys, fp finite_iter_step ys -> xs <<= ys ->
               forall n, Nat.iter n finite_iter_step xs <<= ys.
  Proof.
    intros ST xs ys F H n. apply fInduction.
    -
      exact H.
    -
      intros ys' H'.
      unfold finite_iter_step at 1.
      destruct (pick ys') as [[y [S _]] | _].
      +
        specialize (ST  _ _ S _ H').
        intros x [E |E].
        *
          subst x.
          now apply closure.
        *
          auto.
      +
        exact H'.
  Qed.

  Lemma step_consistent_least_fp
    : step_consistent -> forall xs, least_fp_containing finite_iter_step (finite_iter xs) xs.
  Proof.
    intros ST xs.
    repeat split.
    -
      apply finite_iter_fp.
    -
      apply preservation_finite_iter.
    -
      intros B [H H'].
      now apply step_trans_fp_incl.
  Qed.

  Lemma dup_free_finite_iter_step xs
    : dup_free xs -> dup_free (finite_iter_step xs).
  Proof.
    intro DA.
    unfold finite_iter_step.
    destruct (pick xs) as [[y [S ne]] | S] ; auto. 
  Qed.

  Lemma dup_free_iter_step n xs
    : dup_free xs -> dup_free (Nat.iter n finite_iter_step xs).
  Proof.
    induction n.
    -
      now cbn.
    -
      intro H.
      simpl. apply dup_free_finite_iter_step ; tauto.
  Qed.

  Lemma dup_free_finite_iter xs
    : dup_free xs -> dup_free (finite_iter xs).
  Proof.
    apply dup_free_iter_step.
  Qed.
End FiniteIteration.

Arguments finite_iter {A} step {step_dec} x.
Arguments finite_iter_step {A} step {step_dec} xs.
Arguments pick {A} {step} {step_dec} xs.


