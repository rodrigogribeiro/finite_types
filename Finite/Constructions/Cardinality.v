Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Finite.Constructions.Vector
        Tactics.Tactics.

Import ListNotations.


Lemma Cardinality_gt_zero (A : finType) (x : A) : Cardinality A > 0.
Proof.
  pose proof (element_In x).
  unfold Cardinality.
  destruct (elem A) ; crush.
Qed.

Lemma Cardinality_card_eq (A : finType)
  : card (elem A) = Cardinality A.
Proof.
  apply dup_free_card ; auto.
  apply dup_free_elem.
Qed.

Lemma card_upper_bound (A : finType) (xs : list A): card xs <= Cardinality A.
Proof.
  rewrite <- Cardinality_card_eq.
  apply card_le ; auto.
Qed.  

Lemma injective_dupfree
      (A B : finType)
      (xs : list A)
      (f : A -> B)
  : injective f -> dup_free (get_image f).
Proof.
  intro inj. unfold injective in inj.
  unfold get_image. apply dup_free_map.
  -
    firstorder.
  -
    apply dup_free_elem.
Qed.

Lemma dup_free_length
      (A : finType)
      (xs : list A)
  : dup_free xs -> |xs| <= Cardinality A.
Proof.
  unfold Cardinality.  intros D.
  rewrite <- (dup_free_card _ D). rewrite <- (dup_free_card _ (dup_free_elem A)).
  apply card_le ; auto.
Qed.

Theorem pidgeon_hole_inj
        (A B : finType)
        (f : A -> B)
        (inj : injective f)
  : Cardinality A <= Cardinality B.
Proof.
  rewrite <- (get_image_length f).
  apply dup_free_length.
  apply (injective_dupfree (elem A) inj).
Qed.

Lemma surj_sub
      (A B : finType)
      (f : A -> B)
      (surj : surjective f)
  : elem B <<= get_image f.
Proof.
  intros y E.
  specialize (surj y).
  destruct surj as [x H].
  subst y.
  apply get_image_in.
Qed.


Lemma card_length_leq
      (A : discType)
      (xs : list A) : card xs <= length xs.
Proof.
  induction xs ; repeat (crush ; dec).
Qed.

Theorem pidgeon_hole_surj
        (A B : finType)
        (f : A -> B)
        (surj : surjective f)
  : Cardinality A >= Cardinality B.
Proof.
  rewrite <- (get_image_length f).
  rewrite <- Cardinality_card_eq.
  pose proof (card_le (surj_sub surj)) as H.
  pose proof (card_length_leq (get_image f)) as H'. omega.
Qed.

Lemma eq_iff (x y: nat) : x >= y /\ x <= y -> x = y.
Proof.
  omega.
Qed.

Corollary pidgeon_hole_bij
          (A B : finType)
          (f : A -> B)
          (bij : bijective f)
  : Cardinality A = Cardinality B.
Proof.
  destruct bij as [inj surj]. apply eq_iff. split.
  -
    now eapply pidgeon_hole_surj.
  -
    eapply pidgeon_hole_inj; eauto.
Qed.    
