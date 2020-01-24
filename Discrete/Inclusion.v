Set Implicit Arguments.

Require Import
        Coq.Classes.Morphisms
        Discrete.DiscType
        Discrete.In
        Tactics.Tactics.

Import ListNotations.

(** definitions of inclusion and equivalence *)

Definition incl {A : discType}(xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Definition equiv {A : discType}(xs ys : list A) : Prop :=
  incl xs ys /\ incl ys xs.

Notation "| A |" := (length A) (at level 65).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A === B" := (equiv A B) (at level 70).

Hint Unfold incl equiv.

(** some facts about inclusion and equivalence *)

Lemma incl_refl {A : discType}
  : forall (xs : list A), incl xs xs.
Proof.
  crush.
Qed.

Hint Resolve incl_refl.

Lemma incl_nil {A : discType}
  : forall (xs : list A), incl nil xs.
Proof.
  crush.
Qed.

Hint Resolve incl_nil.


Lemma incl_cons {A : discType}
  : forall (xs ys : list A) x, In x ys -> incl xs ys -> incl (x :: xs) ys.
Proof.
 induction xs ; intros ; unfolds ; crush.
  +
    unfolds in H0.
    apply H0 ; crush.
  +
    unfolds in H0.
    apply In_cons with (y := a) in H1.
    crush.
Qed.

Hint Resolve incl_cons.

Lemma incl_nil_eq {A : discType}
  : forall (xs : list A), incl xs nil -> xs = nil.
Proof.
  induction xs ; crush.
  unfolds in H.
  specialize (H a).
  assert (Hx : In a (a :: xs)) by crush.
  crush.
Qed.

Lemma incl_cons_nil {A : discType}
  : forall (x : A) xs, ~ incl (x :: xs) nil.
Proof.
  intros x xs H ; unfolds in H ; simpl in *.
  apply (H x) ; left*.
Qed.

Hint Resolve incl_cons_nil.

Lemma incl_tl {A : discType}
  : forall (xs ys : list A) y, incl xs ys -> incl xs (y :: ys).
Proof.
  induction xs ; destruct ys ; intros ; unfolds ; crush.
  apply incl_cons_nil in H ; crush.
  apply incl_cons_nil in H ; crush.
  destruct (decision (a = d)) ; destruct (decision (a = y)) ; crush.
  right ; right*. unfolds in H.
  specialize (H a).
  assert (Hx : In a (a :: xs)) by crush.
  crush.
  destruct (decision (x = y)) ; destruct (decision (x = d)) ; crush.
  right ; right*. unfolds in H.
  specialize (H x).
  apply In_cons with (y0 := a) in H1.
  crush.
Qed.

Hint Resolve incl_tl.

Lemma incl_In {A : discType}
  : forall (xs ys : list A) x, In x xs -> incl xs ys -> In x ys.
Proof.
  intros xs ys x H Hincl ; unfolds in Hincl ; crush.
Qed.

Hint Resolve incl_In.

Lemma incl_appl {A : discType}
  : forall (xs ys zs : list A), incl xs ys -> incl xs (ys ++ zs).
Proof.
  induction xs ; destruct ys ; crush.
  +
    unfolds ; unfolds in H.
    intros. lets J : H H0.
    crush.
  +
    unfolds ; intros.
    assert (In x (d :: ys) \/ In x zs) by (left ; eauto).
    apply In_app_iff in H1.
    crush.
Qed.

Hint Resolve incl_appr.

Lemma incl_appr {A : discType}
  : forall (xs zs ys : list A), incl xs zs -> incl xs (ys ++ zs).
Proof.
  induction xs ; destruct zs ; crush.
  +
    apply incl_cons_nil in H ; crush.
  +
    unfolds ; intros.
    assert (In x ys \/ In x (d :: zs)) by (right ; eauto).
    apply In_app_iff in H1.
    crush.
Qed.

Hint Resolve incl_appr.

Lemma incl_app {A : discType}
  : forall (xs ys zs : list A), incl xs zs -> incl ys zs -> incl (xs ++ ys) zs.
Proof.
  induction xs ; crush.
  +
    unfolds ; intros.
    destruct* (In_app_iff (a :: xs) ys x).
    simpl in *.
    lets J : H2 H1.
    destruct J as [[HJ1 | HJ2] | HJ3].
    substs.
    unfolds in H.
    crush.
    unfolds in H.
    crush.
    unfolds in H.
    crush.
Qed.

Hint Resolve incl_app.

Lemma incl_shift {A : discType}
  : forall (xs ys : list A) x, incl xs ys -> incl (x :: xs) (x :: ys).
Proof.
  induction xs ; destruct ys ; intros ; eauto.
  +
    unfolds ; crush.
  +
    apply incl_cons_nil in H ; crush.
  +
    unfolds ; intros.
    unfolds in H.
    simpl in H0.
    destruct H0 as [H1 | [H2 | H3]] ; substs.
    simpl ; eauto.
    assert (In a (a :: xs)) by left*.
    crush.
    assert (In x0 (a :: xs)) by crush.
    lets J : H H0.
    crush.
Qed.

Lemma incl_lcons {A : discType}
  : forall (xs ys : list A) x, incl (x :: xs) ys <-> In x ys /\ incl xs ys.
Proof.
  induction xs ; intros ys x ; splits* ; intro H ; splits ; eauto.
  +
    unfolds in H ; simpl in *.
    specialize (H x). assert (x = x \/ False) by crush.
    crush.
  +
    unfolds in H ; simpl in *.
    specialize (H x).
    assert (x = x \/ x = a \/ In x xs) by crush.
    crush.
Qed.

Lemma incl_sing {A : discType}
  : forall (xs : list A) x y, incl (x :: xs) (y :: []) -> x = y /\ incl xs (y :: []).
Proof.
  induction xs ; intros x y H ; splits ; eauto.
  +
    unfolds in H ; crush.
    specialize (H x) ; crush.
  +
    unfolds in H ; crush.
    specialize (H x) ; crush.
Qed.

Lemma incl_lrcons {A : discType}
  : forall (xs ys : list A) x, incl (x :: xs) (x :: ys) -> ~ In x xs -> incl xs ys.
Proof.
  induction xs ; intros ; eauto.
  +
    unfolds ; unfolds in H ; intros.
    simpl in *.
    specialize (H x0). crush.
Qed.

Lemma incl_app_left {A : discType} :
  forall (xs ys zs : list A), incl (xs ++ ys) zs -> incl xs zs /\ incl ys zs.
Proof.
  induction xs ; intros ; splits ; eauto.
  unfolds ; unfolds in H ; intros.
  apply H. apply In_app_iff. left*.
Qed.

Instance incl_dec {A : discType} (xs ys : list A) : dec (xs <<= ys).
Proof.
  induction xs as [| x xs IHxs].
  -
    unfolds ; left*.
  -
    unfolds in IHxs.
    decide (x el ys) as [E | E].
    +
      destruct IHxs as [H | H].
      *
        left*.
      *
        right.
        contradict H.
        intros y Hc.
        apply H.
        crush.
    +
      right.
      contradict E. apply E. left*.
Qed.

Instance incl_preorder A :
  PreOrder (@incl A).
Proof.
  constructor; hnf; unfold incl; auto.
Qed.

Instance equi_Equivalence A : 
  Equivalence (@equiv A).
Proof.
  constructor; hnf; firstorder.
Qed.

Instance incl_equi_proper A : 
  Proper (@equiv A ==> @equiv A ==> iff) (@incl A).
Proof.
  hnf. intros B C D. hnf. firstorder.
Qed.

Instance cons_incl_proper A x : 
  Proper (@incl A ==> @incl A) (@cons A x).
Proof.
  hnf. intros xs ys. gen xs ys x. apply incl_shift.
Qed.

Instance cons_equi_proper A x : 
  Proper (@equiv A ==> @equiv A) (@cons A x).
Proof.
  hnf. firstorder.
Qed.

Instance in_incl_proper A x : 
  Proper (@incl A ==> Basics.impl) (@In A x).
Proof.
  intros B C D. hnf. auto.
Qed.

Instance in_equi_proper A x : 
  Proper (@equiv A ==> iff) (@In A x).
Proof.
  intros B C D. firstorder.
Qed.

Instance app_incl_proper A : 
  Proper (@incl A ==> @incl A ==> @incl A) (@app A).
Proof.
  intros B C D E F G ; apply incl_app ; crush.
  apply incl_appl. auto.
Qed.

Instance app_equi_proper A : 
  Proper (@equiv A ==> @equiv A ==> @equiv A) (@app A).
Proof.
  hnf. intros X B D. hnf. intros A' B' E.
  destruct D, E; auto. hnf. crush.
Qed.

Lemma equiv_push {A : discType} (x : A) xs :
  In x xs -> xs === (x :: xs).
Proof.
  auto.
Qed.

Lemma equiv_dup {A : discType} (x : A) xs
  : x :: xs === x :: x :: xs.
Proof.
  hnf ; crush ; hnf ; crush.
Qed.

Lemma equiv_shift {A : discType} (x : A) xs ys :
    (x :: xs) ++ ys === xs ++ (x :: ys).
Proof.
  split ; intros y.
  - intros [ D | D ].
    + subst ; crush.
      rewrite In_app_iff. right ; simpl ; left*.
    + apply In_app_iff in D as [D|D] ; eauto.
      apply In_app_iff ; left*.
  - intros D. apply In_app_iff in D as [D|D].
    +
      rewrite In_app_iff. left ; crush.
    +
      rewrite In_app_iff. 
      simpl in *. destruct D. crush.
      crush.
Qed.

Lemma equiv_rotate {A : discType} (x : A) xs :
    x :: xs === xs ++ [x].
Proof.
  split ; intros y ; simpl.
  - intros [D|D] ; subst ; crush.
    rewrite In_app_iff. right ; crush.
    rewrite In_app_iff. left ; auto.
  - intros D. apply In_app_iff in D as [D|D].
    + auto.
    + apply In_sing in D. auto.
Qed.

Lemma list_sigma_forall {A : discType} xs (p : A -> Prop) (p_dec : forall x, dec (p x)) :
  {x | x el xs /\ p x} + {forall x, x el xs -> ~ p x}.
Proof.
  induction xs as [ | x xs] ; simpl.
  -
    tauto.
  -
    destruct IHxs as [[y [D E]]|D].
    +
      eauto.
    +
      destruct (p_dec x) as [E|E].
      *
        eauto.
      *
        right ; crush.
        apply (D x0) ; auto.
Defined.

Arguments list_sigma_forall {A} xs p {p_dec}.

Instance list_forall_dec {A : discType} xs (p : A -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el xs -> p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall xs (fun x => ~ p x)) as [[x [D E]]|D].
  -
    right. auto.
  -
    left. intros x E. apply dec_DN; auto.
Defined.

Instance list_exists_dec {A : discType} xs (p : A -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el xs /\ p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall xs p) as [[x [D E]]|D].
  -
    unfold dec. eauto.
  -
    right.
    intros [x [E F]] ; exact (D x E F).
Defined.

Lemma list_exists_DM {A : discType} xs (p : A -> Prop) : 
  (forall x, dec (p x)) -> ~ (forall x, x el xs -> ~ p x) -> exists x, x el xs /\ p x.
Proof.
  intros D E.
  destruct (list_sigma_forall xs p) as [F | F].
  +
    destruct F as [x F] ; eauto.
  +
    contradiction (E F).
Qed.

Lemma list_exists_not_incl {A : discType} (xs ys : list A) :
  eq_dec A -> 
  ~ xs <<= ys -> exists x, x el xs /\ ~ x el ys.
Proof.
  intros D E.
  apply list_exists_DM ; auto.
  intros F. apply E. intros x G.
  apply dec_DN ; auto.
Qed.

Lemma list_cc {A : discType} (p : A -> Prop) xs : 
  (forall x, dec (p x)) -> 
  (exists x, x el xs /\ p x) -> {x | x el xs /\ p x}.
Proof.
  intros D E.
  destruct (list_sigma_forall xs p) as [[x [F G]]|F].
  -
    eauto.
  -
    exfalso.
    destruct E as [x [G H]].
    apply (F x) ; auto.
Defined.

Definition inclp (A : discType) (xs : list A) (p : A -> Prop) : Prop :=
  forall x, x el xs -> p x.
