Set Implicit Arguments.

Require Import
        Coq.Classes.Morphisms
        Discrete.DiscType
        Discrete.Filter
        Discrete.In
        Discrete.Inclusion
        Discrete.Remove
        Tactics.Tactics.

Import ListNotations.

(** definition of cardinality of a list. *)

Section CARDINALITY.
  Variable A : discType.
  Context {eq_A_dec : eq_dec A}.

  Fixpoint card (xs : list A) : nat :=
    match xs with
    | [] => 0
    | (x :: xs) => if decision (In x xs) then card xs else 1 + card xs
    end.

  Lemma card_in_rem (x : A)(xs : list A) :
    x el xs -> card xs = 1 + card (rem xs x).
  Proof.
    intros D ; induction xs as [ | y xs] ; simpl.
    -
      contradiction D.
    -
      decide (y <> x) ; simpl.
      +
        rewrite IHxs.
        *
          decide (y el xs) ;
          rewrite rem_fst' ; crush ;
            decide (y el rem xs x) ; crush ;
              (reflexivity || exfalso) ; crush ; eauto.
        * 
          destruct D ; crush.
      +
        apply dec_DN in n ; eauto ; substs.
        decide (x el xs).
        *
          rewrite IHxs.
          rewrite rem_fst. crush. auto.
        *
          rewrite rem_id in IHxs ; auto.
          rewrite rem_fst.
          apply rem_id with (eq_A_dec := eq_A_dec) in n.
          crush.
  Qed.

  Lemma card_not_in_rem xs x :
    ~ x el xs -> card xs = card (rem xs x).
  Proof.
    intros D; rewrite rem_id; auto.
  Qed.

  Lemma card_le xs ys :
    xs <<= ys -> card xs <= card ys.
  Proof.
    revert ys.
    induction xs as [|x xs] ; intros B D ; simpl.
    - omega.
    - apply incl_lcons in D as [D D1].
      decide (x el xs) as [E|E].
      + auto.
      + rewrite (card_in_rem D).
        cut (card xs <= card (rem B x)). omega. 
        apply IHxs. auto.
  Qed.

  Lemma card_eq xs ys :
    xs === ys -> card xs = card ys.
  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. omega.
  Qed.

  Lemma card_cons_rem x xs :
    card (x :: xs) = 1 + card (rem xs x).
  Proof.
    rewrite (card_eq (rem_equi x xs)). simpl.
    decide (x el rem xs x) as [D|D].
    - exfalso. apply In_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 xs :
    card xs = 0 -> xs = nil.
  Proof.
    destruct xs as [ | x xs] ; intros D.
    -
      reflexivity.
    -
      exfalso. rewrite card_cons_rem in D. omega.
  Qed.

  Lemma card_ex xs ys :
    card xs < card ys -> exists x, x el ys /\ ~ x el xs.
  Proof.
    intros D.
    decide (ys <<= xs) as [E|E].
    -
      exfalso.
      apply card_le in E.
      omega.
    -
      apply list_exists_not_incl ; auto.
  Qed.

  Lemma card_equiv xs ys :
    xs <<= ys -> card xs = card ys -> xs === ys.
  Proof.
    revert ys.
    induction xs as [| x xs] ; simpl ; intros B D E.
    -
      symmetry in E.
      apply card_0 in E.
      now rewrite E.
    -
      apply incl_lcons in D as [D D1].
      decide (x el xs) as [F|F].
      +
        rewrite (IHxs B) ; auto.
      +
        rewrite (IHxs (rem B x)).
        *
          symmetry.
          apply rem_reorder, D.
        *
          auto.
        *
          apply card_in_rem in D. omega.
  Qed.
  
  Lemma card_lt xs ys x :
    xs <<= ys -> x el ys -> ~ x el xs -> card xs < card ys.
  Proof.
    intros D E F.
    decide (card xs = card ys) as [G|G].
    +
      exfalso.
      apply F.
      apply (card_equiv D) ; auto.
    +
      apply card_le in D.
      omega.
  Qed.
  
  Lemma card_or xs ys :
    xs <<= ys -> xs === ys \/ card xs < card ys.
  Proof.
    intros D.
    decide (card xs = card ys) as [F|F].
    -
      left.
      apply card_equiv ; auto.
    -
      right.
      apply card_le in D. omega.
  Qed.
End CARDINALITY.

Arguments card {A} xs.

Instance card_equi_proper {A : discType} (D : eq_dec A) : 
  Proper (@equiv A ==> eq) (@card A).
Proof.
  hnf. apply card_eq. auto.
Qed.