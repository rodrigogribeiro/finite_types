Set Implicit Arguments.

Require Import
        Discrete.Card
        Discrete.DiscType
        Discrete.Disjoint
        Discrete.Filter
        Discrete.In
        Discrete.Inclusion
        Tactics.Tactics.

Import ListNotations.

(** predicate for duplicate free lists *)

Inductive dup_free {A : discType} : list A -> Prop :=
| DupFree_nil  : dup_free []
| DupFree_cons : forall x xs, ~ x el xs -> dup_free xs -> dup_free (x :: xs).

Hint Constructors dup_free.

(** facts about dup_free *)

Section DUPFREE.
  Variable A : discType.

  Lemma dup_free_cons (x : A) xs :
    dup_free (x :: xs) <-> ~ x el xs /\ dup_free xs.
  Proof.
    split ; intros D.
    -
      inverts D ; auto.
    -
      apply DupFree_cons ; tauto.
  Qed.

  Lemma dup_free_app (xs ys : list A) :
    xs # ys -> dup_free xs -> dup_free ys -> dup_free (xs ++ ys).
  Proof.
    intros D E F. induction E as [|x xs E' E]; simpl.
    -
      exact F.
    -
      apply disjoint_cons in D as [D D'].
      constructor ; [ |exact (IHE D')].
      intros G. apply In_app_iff in G ; tauto.
  Qed.

  Lemma dup_free_map {B : discType} xs (f : A -> B) :
    (forall x y, x el xs -> y el xs -> f x = f y -> x = y) -> 
    dup_free xs -> dup_free (map f xs).
  Proof.
    intros D E. induction E as [|x xs E' E]; simpl ; crush.
    -
      constructor ; [|now auto].
      intros F. apply In_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dup_free_filter (p : A -> Prop)(p_dec : forall x, dec (p x)) xs :
    dup_free xs -> dup_free (filter p xs).
  Proof.
    intros D. induction D as [|x xs C D]; simpl.
    -
      left.
    -
      decide (p x) as [E|E]; [|exact IHD].
      right; [|exact IHD].
      intros F. apply C. apply filter_incl in F. exact F.
   Qed.

  Lemma dup_free_dec (xs : list A) :
    eq_dec A -> dec (dup_free xs).
  Proof.
    intros D. induction xs as [|x xs].
    -
      left*.
    -
      decide (x el xs) as [E | E].
      +
        right*.
        intros F.
        inverts* F.
      +
        destruct (IHxs) as [F|F].
        *
          unfold dec.
          auto.
        *
          right*. intros G. inverts* G. 
  Qed.

  Lemma dup_free_card (xs : list A) (eq_A_dec : eq_dec A) :
    dup_free xs -> card xs = | xs |.
  Proof.
    intros D.
    induction D as [|x xs E F] ; simpl ; crush.
    - decide (x el xs) as [G | ] ; crush.
  Qed.
End DUPFREE.

Section UNDUP.

  Variable A : discType.
  Context {eq_A_dec : eq_dec A}.

  Fixpoint undup (xs : list A) : list A :=
    match xs with
    | [] => []
    | y :: ys => if decision (y el ys) then undup ys
                else y :: undup ys
    end.

  Lemma undup_id_equiv (xs : list A) :
    undup xs === xs.
  Proof.
    induction xs as [|x xs]; simpl ; crush.
    -
      decide (x el xs) as [E|E] ; crush.
  Qed.

 Lemma dup_free_undup xs :
    dup_free (undup xs).
  Proof.
    induction xs as [|x xs] ; simpl ; crush.
    -
      decide (x el xs) as [E|E] ; crush.
      right ; auto. now rewrite undup_id_equiv.
  Qed.

  Lemma undup_incl xs ys :
    xs <<= ys <-> undup xs <<= undup ys.
  Proof.
    now rewrite !undup_id_equiv.
  Qed.

  Lemma undup_equi xs ys :
    xs === ys <-> undup xs === undup ys.
  Proof.
    now rewrite !undup_id_equiv.
  Qed.

  Lemma undup_id xs :
    dup_free xs -> undup xs = xs.
  Proof.
    intros E. induction E as [|x xs E F] ; crush.
    -
      decide (x el xs) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent xs :
    undup (undup xs) = undup xs.

  Proof.
    apply undup_id, dup_free_undup.
  Qed.
End UNDUP.

Lemma dup_free_concat
      (A : discType) (xs : list (list A))
  : (forall ys, ys el xs -> dup_free ys) /\
    (forall ys zs, ys <> zs -> ys el xs -> zs el xs -> disjoint ys zs) ->
    dup_free xs -> dup_free (concat xs).
Proof.
  induction xs as [| x xs].
  -
    constructor.
  -
    intros [H H'] D. cbn. apply dup_free_app.
    +
      apply disjoint_concat.
      intros C E.
      apply H'; auto. inverts D.
      intro G ; apply H2 ; now subst x. crush. crush. 
    +
      apply H. crush.
    +
      inverts D ; apply IHxs ; crush.
Qed.     

Arguments undup {A} xs.