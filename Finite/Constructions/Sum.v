Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.

Definition to_sum_listl {A : Type}  (B : Type) (xs : list A): list (A + B) :=
  map inl xs.

Definition to_sum_listr {B : Type}  (A : Type) (xs : list B): list (A + B) :=
  map inr xs.

Lemma count_to_sum_listl {A : discType}  (B : discType) (xs : list A) x
  : count (to_sum_listl B xs) (inl x) = count xs x.
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma count_to_sum_listr {B : discType}  (A : discType) (xs : list B) x
  : count (to_sum_listr A xs) (inr x) = count xs x.
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma count_to_sum_listl_zero {A : discType}(B : discType)(xs : list A)(y : B)
  : count (to_sum_listl B xs) (inr y) = 0.
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma count_to_sum_listr_zero {B : discType}(A : discType)(xs : list B)(x : A)
  : count (to_sum_listr A xs) (inl x) = 0.
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma prove_one m n : m = 1 /\ n = 0 \/ n = 1 /\ m = 0 -> m + n = 1.
Proof.
  omega.
Qed.

Lemma to_sum_listl_missing (A B : discType) (y : B) (xs : list A)
  : count (to_sum_listl B xs) (inr y) = 0.                           
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma to_sum_listr_missing (A B : discType) (x : A) (xs : list B)
  : count (to_sum_listr A xs) (inl x) = 0.                           
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma sum_enum_sound (A : finType) (B : finType) x :
  count (to_sum_listl B (elem A) ++ to_sum_listr A (elem B)) x = 1.
Proof.
  rewrite count_app. apply prove_one. destruct x.
  -
    left. split.
    +
      rewrite count_to_sum_listl. apply enum_sound.
    +
      apply to_sum_listr_missing.
  - right. split.
    +
      rewrite count_to_sum_listr. apply enum_sound.
    +
      apply to_sum_listl_missing.
Qed.

Instance FinTypeC_sum (A B : finType) : FinTypeC (DiscSum A B).
Proof.
  econstructor. apply sum_enum_sound.
Defined.

Canonical Structure FinType_sum (A B : finType) : finType := FinType (DiscSum A B).
Notation "A (+) B" := (FinType_sum A B) (at level 50, left associativity).


Lemma cardinality_sum (A B : finType)
  : Cardinality (FinType_sum A B) = Cardinality A + Cardinality B.
Proof.
  unfold Cardinality.
  cbn.
  rewrite app_length.
  unfold to_sum_listl, to_sum_listr. now repeat rewrite map_length.
Qed.
