Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.


Fixpoint to_sigma_list (A : Type) (f : A -> finType) (xs : list A) : list (sigT f) :=
  match xs with
  | [] => []
  | x :: xs' => (map (existT f x) (elem (f x))) ++ to_sigma_list f xs'
  end.

Lemma count_map_existT
      (A : discType)
      (f : A -> discType)
      (x : A)(xs : list (f x))(y : f x)
  : count (map (existT f x) xs) (existT f x y) = count xs y.
Proof.
  induction xs as [| x' xs] ; crush.
  -
    dec ; auto.
    +
      contradict n. exact (sigT_proj2_fun _ e).
    +
      subst x'. contradict n. reflexivity.
Qed.      

Lemma count_map_existT_zero
      (A : discType)
      (f : A -> discType)
      (x x' : A) (xs : list (f x)) (y : f x')
  : x <> x' -> count (map (existT f x) xs) (existT f x' y) = 0.
Proof.
  intros E. induction xs as [| x1 xs] ; repeat (crush ; dec).
Qed.

Lemma to_sigma_list_count
      (A : discType)
      (f : A -> finType)
      (xs : list A)
      (s: sigT f)
  : count (to_sigma_list f xs) s = count xs (projT1 s).
Proof.
  induction xs as [| x xs] ; crush.
  -
    destruct s. cbn in *.
    rewrite count_app. rewrite IHxs. dec.
    + change (S (count xs x)) with (1 + count xs x). f_equal. subst x.
      rewrite (@count_map_existT _ f _ (elem (f _)) _). 
      unfold elem. rewrite enum_sound. crush.
    +
      change (count xs x) with (0 + (count xs x)). f_equal.
      rewrite (@count_map_existT_zero _ f _ _); auto.
Qed.

Lemma sigma_enum_sound
      (A : finType)
      (f : A -> finType)
      (s : sigT f)
  : count (to_sigma_list f (elem A)) s = 1.
Proof.
  rewrite to_sigma_list_count. now pose proof (enum_sound (projT1 s)).
Qed.

Instance FinTypeC_sigma (A : finType) (f : A -> finType): FinTypeC (DiscSigT f).
Proof.
  econstructor.  apply sigma_enum_sound.
Defined.

Canonical Structure FinType_sigma (A : finType) (f : A -> finType) :=
  FinType (DiscSigT f).
