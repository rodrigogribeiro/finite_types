Set Implicit Arguments.

Require Import
        Discrete.DiscType
        Discrete.DupFree
        Discrete.In 
        Tactics.Tactics.

(** function to count the number of an element in
    a list *)

Fixpoint count {A : discType}(xs : list A)(x : A) : nat :=
  match xs with
  | nil => 0
  | (cons y ys) => if decision (x = y) then 1 + (count ys x) else count ys x
  end.

(** some facts about count *)

Lemma count_not_in_iff {A : discType}
  : forall (xs : list A)(x : A), ~ (x el xs) <-> count xs x = 0.
Proof.
  induction xs as [ | x xs] ; crush.
  +
    destruct (decision (x0 = x)) ; crush.
    apply IHxs ; auto.
  +
    destruct (decision (x = x)) ; crush.
  +
    destruct* (decision (x0 = x)) as [G | G]; crush.
    specialize (IHxs x0).
    destruct IHxs. specialize (H2 H) ; crush.
Qed.

Hint Resolve count_not_in_iff.

Lemma count_in_gt_zero {A : discType}
  : forall (xs : list A)(x : A), x el xs <-> count xs x > 0.
Proof.
  induction xs as [| x xs ] ; crush.
  +
    destruct* (decision (x = x)) ; crush.
  +
    destruct* (decision (x0 = x)) ; crush.
    destruct* (IHxs x0) ; crush.
  +
    destruct (decision (x0 = x)) ; crush.
Qed.

Lemma count_in_dupfree {A : discType} (xs : list A) x
  : dup_free xs -> x el xs -> count xs x = 1.
Proof.
  intros H ; revert x ; induction H as [| x xs] ; intros y H1 ; simpl in *.
  +
    crush.
  +
    destruct H1 as [H1 | H1] ; substs.
    *
      decide (x = x) as [G | G].
      - 
        specialize (count_not_in_iff xs x) ; intros H2.
        destruct* H2.
      -
        crush.
    *
      specialize (IHdup_free y H1).
      rewrite IHdup_free.
      decide (y = x) as [G | G] ; substs* ; crush.
Qed.      

Lemma count_lt_dup_free {A : discType}(xs : list A)
  : (forall x, count xs x <= 1) -> dup_free xs.
Proof.
  induction xs as [| x xs] ; eauto.
  -
    intro H. constructor.
    +
      cbn in H.  specialize (H x). decide (x = x).
      assert (Hz : count xs x = 0) by omega. apply count_not_in_iff in Hz ; eauto.
      crush.
    +
      apply IHxs. intro y. specialize (H y). cbn in H. decide (y = x) ; omega.
Qed.

Lemma count_app {A : discType}(xs ys : list A) x
  : count (xs ++ ys) x = count xs x + count ys x.
Proof.
  induction xs ; crush.
  +
    decide (x = a) ; crush.
Qed.

(** dealing with options *)

Definition to_option_list {A : Type} (xs : list A) :=
    None :: map (@Some _) xs.

Lemma count_option_list (A : discType) (xs : list A) x
  : count (to_option_list xs) (Some x) = count xs x .
Proof.
  unfold to_option_list. simpl. dec ; try congruence.
  induction xs ; crush.
  +
    dec ; congruence.
Qed.

(** A list produced by toOptionList contains None exactly once *)

Lemma count_option_list_none (A : discType) (xs : list A)
  : count (to_option_list xs) None = 1.
Proof.
  unfold to_option_list. simpl. dec ; try congruence. f_equal.
    induction xs as [| x xs] ; crush.
  -
    simpl; dec; congruence.
 Qed.

Lemma dup_free_count
      (A : discType)
      (x : A)
      (xs : list A)
  : dup_free xs -> x el xs -> count xs x = 1.
Proof.
  intros D E. induction D.
  -
    contradiction E.
  -
    cbn.
    dec.
    +
      f_equal.
      subst x0.
      apply count_not_in_iff. auto.
    +
      destruct E as [E | E] ; [> congruence | auto].
Qed.        

