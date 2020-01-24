Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.

Fixpoint cartesian_product {A B : Type}(xs : list A)(ys : list B) :=
  match xs with
  | [] => []
  | x :: xs' => map (fun y => (x , y)) ys ++ cartesian_product xs' ys
  end.

Lemma cartesian_product_nil {A B : Type} (xs : list A) :
  cartesian_product xs ([] : list B) = []. 
Proof.
  induction xs ; crush.
Qed.


Section LEMMAS.
  Variables A B : discType.

  Lemma count_map (ys : list B) (x1 : A) y :
    count (map (fun y => (x1,y)) ys) (x1, y) = count ys y.
  Proof.
    induction ys ; crush.
    - simpl. dec ;  congruence.
  Qed.

  Lemma count_map_zero  (ys : list B) (x' x : A)  y
    : x' <> x -> count  (map (fun y => (x,y)) ys) (x', y) = 0.
  Proof.
    intros ineq. induction ys ; repeat (crush ; dec).
  Qed.

  Lemma cartesian_product_count (xs : list A) (ys : list B)(x : A)(y : B)
    : count (cartesian_product xs ys) (x,y) =  count xs x * count ys y.
  Proof.
    induction xs as [| x' xs] ; crush.
    -
      rewrite count_app. rewrite IHxs. decide (x = x') as [E | E] ; substs.
      +
        cbn. fequals*. apply count_map.
      +
        rewrite <- plus_O_n. fequals*. now apply count_map_zero.
  Qed.
End LEMMAS.

Lemma cartesian_product_enum_sound (A B : finType) (x : A * B)
  : count (cartesian_product (elem A) (elem B)) x = 1.
Proof.
  destruct x as [x y]. rewrite cartesian_product_count.
  unfold elem. now rewrite !enum_sound.
Qed.

Instance FinTypeC_Prod (A B : finType) : FinTypeC (A ** B).
Proof.
  econstructor.  apply cartesian_product_enum_sound.
Defined.

Canonical Structure FinType_Prod (A B : finType) := FinType (A ** B).

Notation "A (x) B" := (FinType_Prod A B) (at level 40, left associativity).

Lemma cardinality_cartesian_product {A B : finType}
  : Cardinality (A (x) B) = Cardinality A * Cardinality B.
Proof.
  cbn. unfold cartesian_product. unfold Cardinality.
  induction (elem A) ; crush.
  -
    cbn.
    rewrite app_length.
    rewrite IHl. f_equal. apply map_length.
Qed.

