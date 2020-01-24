Set Implicit Arguments.

Require Import
        Discrete.DiscType
        Discrete.In
        Discrete.Inclusion
        Tactics.Tactics.

Import ListNotations.

Fixpoint filter
         (A : Type)
         (p : A -> Prop)
         (p_dec : forall x, dec (p x))(xs : list A) : list A :=
  match xs with
  | [] => []
  | y :: ys => if decision (p y) then y :: filter p_dec ys
              else filter p_dec ys
  end.

Arguments filter {A} p {p_dec} xs.

Section LEMMAS.
  Variable A : discType.
  Variable p : A -> Prop.
  Context {p_dec : forall x, dec (p x)}.

  Lemma In_filter_iff (x : A) xs :
    x el (filter p xs) <-> x el xs /\ p x.
  Proof.
    induction xs ; simpl.
    -
      tauto.
    -
      decide (p a) ; simpl ; rewrite IHxs ; crush.
  Qed.

  Lemma filter_incl (xs : list A) :
    filter p xs <<= xs.
  Proof.
    intros x D. rewrite In_filter_iff in D. crush.
  Qed.

  Lemma filter_mono (xs ys : list A) :
    xs <<= ys -> filter p xs <<= filter p ys.
  Proof.
    intros D x E. apply In_filter_iff in E as [E E'].
    apply In_filter_iff. auto.
  Qed.

  Lemma filter_id xs :
    (forall x, x el xs -> p x) -> filter p xs = xs.
  Proof.
    intros D.
    induction xs ; simpl.
    - reflexivity.
    - decide (p a) as [E|E] ; crush.
  Qed.

  Lemma filter_app xs ys :
    filter p (xs ++ ys) = filter p xs ++ filter p ys.
  Proof.
    induction xs as [|y xs']; simpl.
    - reflexivity.
    - rewrite IHxs'. decide (p y); reflexivity.
  Qed.

  Lemma filter_fst x xs :
    p x -> filter p (x :: xs) = x :: filter p xs.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

  Lemma filter_fst' x xs :
    ~ p x -> filter p (x :: xs) = filter p xs.
  Proof.
    simpl. decide (p x); tauto.
  Qed.
End LEMMAS.

Section LEMMAS1.
  Variable A : discType.
  Variables p q : A -> Prop. 
  Context {p_dec : forall x, dec (p x)}.
  Context {q_dec : forall x, dec (q x)}.

  Lemma filter_pq_mono xs :
    (forall x, x el xs -> p x -> q x) -> filter p xs <<= filter q xs.
  Proof.
    intros D x E. apply In_filter_iff in E as [E E'].
    lets J : D E E'.
    assert (x el xs /\ q x) by crush.
    rewrite In_filter_iff ; auto.
  Qed.

  Lemma filter_pq_eq xs :
    (forall x, x el xs -> (p x <-> q x)) -> filter p xs = filter q xs.
  Proof.
    intros C ; induction xs as [ |x xs] ; simpl.
    - reflexivity.
    - decide (p x) as [D|D]; decide (q x) as [E|E].
      +
        f_equal. crush.
      +
        exfalso. apply E , (C x) ; crush.
      +
        exfalso. apply D, (C x) ; crush.
      +
        crush.
  Qed.

  Lemma filter_and xs :
    filter p (filter q xs) = filter (fun x => p x /\ q x) xs.
  Proof.
    set (r x := p x /\ q x).
    induction xs as [ | x xs] ; simpl. reflexivity.
    decide (q x) as [E|E]; simpl; rewrite IHxs.
    -
      decide (p x) ; decide (r x) ; unfold r in *|- ; crush.
    -
      decide (r x) ; unfold r in *|- ; crush.
  Qed.
End LEMMAS1.

Section LEMMAS2.
  Variable A : discType.
  Variables p q : A -> Prop. 
  Context {p_dec : forall x, dec (p x)}.
  Context {q_dec : forall x, dec (q x)}.

  Lemma filter_comm xs :
    filter p (filter q xs) = filter q (filter p xs).
  Proof.
    rewrite !filter_and. apply filter_pq_eq. tauto.
  Qed.
End LEMMAS2.