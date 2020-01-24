Set Implicit Arguments.

Require Import
        Discrete.DiscType
        List
        Tactics.Tactics.

Import ListNotations.

(** decidabitity of list membership *)

Fixpoint In {A : discType}(x : A)(xs : list A) : Prop :=
  match xs with
  | [] => False
  | (y :: ys) => x = y \/ In x ys
  end.

Instance In_dec {A : discType} : forall (x : A) xs, dec (In x xs).
Proof.
  intros x xs ; gen x ; induction xs ; intros ; crush.
Qed.

Notation "x 'el' A" := (In x A) (at level 70).

(** facts about In *)

Lemma In_app_iff {A : discType}
  : forall xs ys (x : A), In x (xs ++ ys) <-> In x xs \/ In x ys.
Proof.
  induction xs ; intros ; crush.
  +
    destruct* (IHxs ys x) ; crush.
Qed.

Hint Resolve In_app_iff.

Lemma In_rev_iff {A : discType}
  : forall xs (x : A) , In x (rev xs) <-> In x xs.
Proof.
  induction xs ; crush ; try solve [apply In_app_iff ; crush].
  +
    apply In_app_iff in H ; crush.
    destruct* (IHxs x) ; right*.
Qed.

Hint Resolve In_rev_iff.


Lemma In_map {A B : discType}
  : forall (xs : list A)(f : A -> B)(x : A),
    In x xs -> In (f x) (map f xs).
Proof.
  induction xs ; crush.
Qed.


Lemma In_map_iff {A B : discType}
  : forall (xs : list A)(f : A -> B)(x : B),
    In x (map f xs) <-> exists (y : A), f y = x /\ In y xs.
Proof.
  induction xs ; intros f x ; splits ; intros H ; try solve [crush].
  +
    simpl in *.
    destruct H. exists* a.
    destruct (IHxs f x) as [Hl Hr].
    specialize (Hl H). crush. eexists ; eauto.
  +
    crush.
    apply In_map with (f0 := f) in H.
    destruct (IHxs f (f x0)) as [Hl Hr].
    specialize (Hl H).
    crush ; eexists ; eauto.
Qed.

Hint Resolve In_map.

Lemma In_eq {A : discType}
  : forall (xs : list A) x, In x (x :: xs).
Proof.
  crush.
Qed.

Lemma In_cons {A : discType}
  : forall (xs : list A) x y, In x xs -> In x (y :: xs).
Proof.
  induction xs ; crush.
Qed.

Lemma In_nil {A : discType}
  : forall (x : A), ~ In x nil.
Proof.
  crush.
Qed.

Lemma In_sing {A : discType}
  : forall (x y : A), In x (y :: []) -> x = y.
Proof.
  crush.
Qed.

Lemma In_cons_neq {A : discType}
  : forall (xs : list A) x y, In x (y :: xs) -> x <> y -> In x xs.
Proof.
  induction xs ; crush.
Qed.

Lemma not_In_cons {A : discType}
  : forall (xs : list A) x y, ~ In x (y :: xs) -> x <> y /\ ~ In x xs.
Proof.
  induction xs ; crush.
Qed.
