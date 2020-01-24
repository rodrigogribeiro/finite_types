Set Implicit Arguments.

Require Import
        Discrete.DiscType
        Discrete.Filter
        Discrete.In
        Discrete.Inclusion
        Tactics.Tactics.

Section REM.
  Variable A : discType.
  Context {eq_A_dec : eq_dec A}.

  Definition rem (xs : list A) x :=
    filter (fun y => y <> x) xs.

  Lemma In_rem_iff x xs y :
    x el rem xs y <-> x el xs /\ x <> y.
  Proof.
    apply In_filter_iff.
  Qed.

  Lemma rem_not_in x y xs :
    x = y \/ ~ x el xs -> ~ x el rem xs y.
  Proof.
    intros D E. apply In_rem_iff in E. tauto.
  Qed.

  Lemma rem_incl xs x :
    rem xs x <<= xs.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono xs ys x :
    xs <<= ys -> rem xs x <<= rem ys x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons xs ys x :
    xs <<= ys -> rem (x :: xs) x <<= ys.
  Proof.
    intros E y F. apply E. apply In_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Hint Resolve rem_cons.

  Lemma rem_cons' xs ys x y :
    x el ys -> rem xs y <<= ys -> rem (x :: xs) y <<= ys.
  Proof.
    intros E F u G.
    apply In_rem_iff in G. crush.
    apply F. apply In_rem_iff. splits*. 
  Qed.

  Lemma rem_in x y xs :
    x el rem xs y -> x el xs.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y xs :
    x <> y -> x el xs -> x el rem xs y.
  Proof.
    intros E F. apply In_rem_iff. auto.
  Qed.

  Hint Resolve rem_in rem_neq.

  Lemma rem_app x xs ys :
    x el xs -> ys <<= xs ++ rem ys x.
  Proof.
    intros E y F. decide (x=y) as [[]|] ;
      try apply In_app_iff ; crush.
  Qed.

  Lemma rem_app' x xs ys zs :
    rem xs x <<= zs -> rem ys x <<= zs -> rem (xs ++ ys) x <<= zs.
  Proof.
    unfold rem ; rewrite filter_app ; auto.
  Qed.

  Lemma rem_equi x xs :
    x :: xs === x :: rem xs x.
  Proof.
    split ; intros y; 
    intros [[]|E] ; decide (x=y) as [[]|D] ; crush ; eauto.
  Qed.

  Lemma rem_comm xs x y :
    rem (rem xs x) y = rem (rem xs y) x.
  Proof.
    apply filter_comm.
  Qed.

  Lemma rem_fst x xs :
    rem (x :: xs) x = rem xs x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y xs :
    x <> y -> rem (x :: xs) y = x :: rem xs y.
  Proof.
    intros E. unfold rem. rewrite filter_fst ; auto.
  Qed.

  Lemma rem_id x xs :
    ~ x el xs -> rem xs x = xs.
  Proof.
    intros D. apply filter_id.
    intros y E F. subst. auto.
  Qed.

  Lemma rem_reorder x xs :
    x el xs -> xs === x :: rem xs x.
  Proof.
    intros D. rewrite <- rem_equi. apply equiv_push, D.
  Qed.

  Lemma rem_inclr xs ys x :
    xs <<= ys -> ~ x el xs -> xs <<= rem ys x.
  Proof.
    intros D E y F. apply In_rem_iff.
    intuition; subst; auto.
  Qed.
End REM.

Arguments rem {A}{eq_A_dec} xs x.

Hint Resolve rem_not_in rem_incl rem_mono
     rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr.
