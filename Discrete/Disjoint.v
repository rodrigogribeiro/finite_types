Set Implicit Arguments.

Require Import
        Discrete.DiscType
        Discrete.In
        Discrete.Inclusion.

Section DISJOINT.
  Variable A : discType.

  Definition disjoint (xs ys : list A) :=
    ~ exists x, x el xs /\ x el ys.

  Notation "xs '#' ys" := (disjoint xs ys)(at level 60, right associativity).

  Lemma disjoint_forall (xs ys : list A) :
     xs # ys <-> forall x, x el xs -> ~ x el ys.
  Proof.
    split.
    -
      intros D x E F. apply D. exists x. auto.
    -
      intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm (xs ys : list A) :
    xs # ys -> ys # xs.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl (xs ys zs : list A) :
    zs <<= ys -> xs # ys -> xs # zs.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil (xs : list A) :
    nil # xs.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' (xs : list A) :
    xs # nil.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_cons x xs ys :
     (x :: xs) # ys <-> ~ x el ys /\ xs # ys.
  Proof.
    split.
    - intros D. split.
      +
        intros E.
        apply D. eexists ; splits ; crush.
      +
        intros [y [E F]]. apply D.
        exists y ; crush.
    -
      intros [D E] [y [[F|F] G]].
      +
        congruence.
      +
        apply E. eauto.
  Qed.

  Lemma disjoint_app (xs ys zs : list A) :
    (xs ++ ys) # zs <-> xs # zs /\ ys # zs.
  Proof.
    split.
    -
      intros D. split.
      +
        intros [x [E F]]. apply D.
        exists x ; rewrite In_app_iff ; crush.
      +
        intros [x [E F]]. eauto 6.
    -
      intros [D E] [x [F G]].
      apply In_app_iff in F as [F|F] ; eauto.
  Qed.

  Lemma disjoint_concat (xs : list (list A)) (ys : list A)
    : (forall zs, zs el xs -> disjoint ys zs) -> disjoint ys (concat xs).
  Proof.
    intros H. induction xs as [|x xs].
    -
      simpl ; unfolds ; crush.
    -
      cbn.
      apply disjoint_symm. apply disjoint_app.
      split.
      +
        unfolds ; crush.
        assert (Hc : ys # x).
        *
          apply H ; left*.
        *
          unfolds in Hc. apply Hc.
          exists x0 ; crush.
      +
        apply disjoint_symm.
        apply IHxs. intros zs Hzs.
        apply H. crush.
Qed.

End DISJOINT.

Arguments disjoint {A} xs ys.

Hint Resolve disjoint_nil disjoint_nil'.

Notation "xs '#' ys" := (disjoint xs ys)(at level 60, right associativity).
