Set Implicit Arguments.

Require Import
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.


Fixpoint to_subtype_list
         (A : Type)
         (xs : list A)
         (p : A -> Prop) (D : forall x, dec (p x)) : list (subtype p) :=
  match xs with
  | nil => nil
  | x :: xs' => match decision (p x) with
               | left px => (exist  _ x (purify px)) :: to_subtype_list xs' D
               | right _ => to_subtype_list xs' _
               end
  end.

Arguments to_subtype_list {A} xs p {D}.

Lemma to_subtype_list_count
      (A : discType) (p: A -> Prop) (xs : list A) (D : forall x, dec (p x)) x
  : count (to_subtype_list xs p) x = count xs (proj1_sig x).
Proof.
  induction xs as [| x' xs] ; crush.
  -
    decide (p x').
    +
      simpl. dec ; crush.
      * now rewrite <- subtype_extensionality in *.
    + destruct x.
      cbn.
      dec ; crush ;  now impurify p0.
Qed.

Lemma subtype_enum_sound (A : finType)(p : A -> Prop) (D : forall x, dec (p x)) x
  : count (to_subtype_list (elem A) p) x = 1.
Proof.
  rewrite to_subtype_list_count. apply enum_sound.
Qed.

Instance FinTypeC_subtype
         (A : finType)
         (p : A -> Prop) (D : forall x, dec (p x)) : FinTypeC (DiscSubtype p).
Proof.
  econstructor. apply subtype_enum_sound.
Defined.

Canonical Structure FinType_subtype
          (A : finType)
          (p : A -> Prop) (D : forall x, dec (p x)) := FinType (DiscSubtype p).

Arguments FinType_subtype {A} p {_}.

Lemma in_undup (A : discType) (xs : list A) x : x el xs <-> x el (undup xs).
Proof.
  now rewrite undup_id_equiv.
Qed.


Lemma enum_sound_from_list (A : discType) (xs : list A) x
  : count (undup (to_subtype_list xs (fun x => x el xs))) x = 1.
Proof.
  apply count_in_dupfree.
  -
    apply dup_free_undup.
  -
    rewrite <- in_undup.
    apply count_in_gt_zero. rewrite to_subtype_list_count.
    destruct x as [x p]. cbn. apply count_in_gt_zero. now impurify p.
Qed.

Instance FromListC (A : discType) (xs : list A)
  : FinTypeC (DiscSubtype (fun x => x el xs)).
Proof.
  econstructor. intros [x p]. apply enum_sound_from_list.
Defined.

Canonical Structure FinType_from_list (A : discType) (xs : list A)
  := FinType (DiscSubtype (fun x => x el xs)).

Lemma finType_from_list_correct (A : discType) (xs : list A)
  : map (@proj1_sig _ _) (elem (FinType_from_list xs)) === xs.
Proof.
  cbn. split.
  -
    intros x H.
    destruct (In_map_iff (undup (to_subtype_list xs (fun x => x el xs)))
                         (@proj1_sig _ _)
                         x) as [Hl Hr].
    crush. destruct x0.
    now impurify p.
  -
    intros x H.
    specialize (In_map_iff (undup (to_subtype_list xs (fun x => x el xs)))
                         (@proj1_sig _ _)
                         x) ; intros Hiff.
    destruct Hiff as [Hl Hr].
    apply Hr.
    eexists. Unshelve.
    2:{
      exists x. unfold pure. now dec.
    }
    + cbn. split; auto.
      apply count_in_gt_zero with (xs0 := undup (to_subtype_list xs _)).
      rewrite enum_sound_from_list. omega.
Qed.
