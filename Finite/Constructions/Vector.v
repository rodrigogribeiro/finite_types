Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.

(** xs is a vector (list) indexed by A's elements *)

Definition Card_X_eq A B (xs : list B) := |xs| = Cardinality A.

Definition vector (A : finType) (B : Type) := subtype (@Card_X_eq A B).
Notation "A --> B" := (vector A B) (at level 55, right associativity).

(** image of a vector *)

Definition image (A : finType) (B : Type) (f : A --> B) := proj1_sig  f.

Instance vector_eq_dec (X: finType) (Y: discType) : eq_dec (X --> Y).
Proof.
  crush.
Qed.

Canonical Structure DiscVect (A : finType)(B: discType) := DiscType (A --> B).

Fixpoint images (B : Type) (xs : list B) (n: nat): list (list B) :=
  match n with
  | 0 => [[]]
  | S n' => concat (map (fun x => map (cons x) (images xs n')) xs)
  end.

Lemma images_not_nil (A : Type) x (xs : list A) : forall n, images (x :: xs) n <> nil.
Proof.
  intro n. induction n as [| n'].
  -
    crush.
  -
    cbn. intro H. pose proof (app_eq_nil _ _ H) as [E1 E2]. clear H.
    pose proof (map_eq_nil _ _ E1).  auto.
Qed.

Lemma not_In_map_cons (A : discType) (y x : A) (xs : list A) (ys : list (list A))
  : y <> x -> (x :: xs) el (map (cons y) ys) -> False.
Proof.
  intros neq E. rewrite In_map_iff in E. destruct E as [C [E _]]. congruence.
Qed.

Definition mC A xs := (fun x : A => map (cons x) xs).
Definition mmC A xs (ys : list A) := map (mC xs) ys.

Lemma disjoint_map_cons (A : discType) (xs : list (list A)) (x y : A )
  : x <> y -> disjoint (map (cons x) xs) (map (cons y) xs).
Proof.
  intro N ; induction xs as [| x' xs].
  -
    cbn. auto.
  -
    cbn. unfold disjoint. intros [B [H1 H2]]. destruct H1, H2 ; try solve [crush].
    +
      subst B.
      eapply not_In_map_cons with (A := A)(y := y)(x := x)(xs := x')(ys := xs) ; auto.
    +
      subst B.
      eapply not_In_map_cons ; eauto.
    +
      apply IHxs. now exists B.
Qed.  

Lemma disjoint_in
      (A : discType) x xs
      (ys : list (list A))
      (E : ys <> nil) zs
      (H: ~ x el xs)
  : zs el map (mC ys) xs -> disjoint (map (cons x) ys) zs.
Proof.
  destruct ys ; try congruence.
  intro H'. induction xs as [| x' xs].
  -
    contradiction H'.
  -
    pose proof (neg_or H) as [G G']. destruct H' as [H' | H'].
    +
      subst zs. apply disjoint_map_cons; congruence.
    +
      apply IHxs ; auto.
Qed.


Lemma disjoint_in_map_map_cons
      (A : discType) (xs : list A)
      (ys zs zs' : list (list A))
      (H : zs <> zs')
      (E : zs el (mmC ys xs))
      (E': zs' el (mmC ys xs))
      (N : ys <> nil)
      (D : dup_free xs):
  disjoint zs zs'.
Proof. 
  induction D.
  -
    contradiction E.
  -
    destruct ys ; try congruence ; clear N.
    destruct E, E'; try congruence.
    +
      subst zs.
      eapply disjoint_in ; now eauto.
    +
      subst zs'.
      apply disjoint_symm.
      eapply disjoint_in ; now eauto.
    +
      now apply IHD.
Qed.      
  
Lemma dup_free_concat_map_cons (A : discType) (xs : list A) (ys : list (list A))
  : dup_free xs ->
    dup_free ys ->
    ys <> nil ->
    dup_free (concat (map (fun x => map (cons x) ys) xs)).
Proof.
  intros D D' N.
  apply dup_free_concat ; try split.
  -
    intros C E. induction D.
    +
      contradiction E.
    +
      destruct E ; auto. subst C.
      apply dup_free_map ; auto.
      congruence.
  -
    intros B' B'' E E' H.
    eapply disjoint_in_map_map_cons; eauto.
  -
    apply dup_free_map ; auto.
    intros x y _ _ E.
    destruct ys.
    +
      congruence.
    +
      cbn in E. now inverts E.
Qed.

Lemma images_dup_free
      (A : discType)
      (xs : list A)
      (n : nat)
  : dup_free xs -> dup_free (images xs n).
Proof.
  induction n as [| n].
  -
    now repeat constructor.
  -
    cbn.
    intro D.
    destruct xs.
    +
      constructor.
    +
      apply dup_free_concat_map_cons ; auto.
      apply images_not_nil.
Qed.

Lemma in_concat_cons (A : discType)(xs zs : list A) (ys : list (list A)) y
  : y el xs /\ zs el ys -> (y :: zs) el (concat (map (fun x => map (cons x) ys) xs)).
Proof.
  intros [E E']. induction xs as [| x xs].
  -
    contradiction E.
  -
    cbn. destruct E as [E | E].
    +
      subst x.
      apply In_app_iff.
      left.
      apply In_map_iff.
      now exists zs.
    +
      apply In_app_iff. crush.
Qed.                                                               
    
Lemma in_images (A : discType) (xs ys : list A)
  : (forall x, x el ys -> x el xs) -> ys el images xs (|ys|).
Proof.
 intros E. induction ys as [| y ys].
 -
   cbn.
   now left.
 -
   cbn. apply in_concat_cons. crush.
Qed.

Lemma dup_free_elem (A : finType) : dup_free (elem A).
Proof.
  destruct A as [X [A AI]]. assert (forall x, count A x <= 1) as H'.
  {
    intro x. specialize (AI x). omega.
  }
  now apply count_lt_dup_free.  
Qed.


Lemma vector_enum_sound (A : finType) (B : finType) f
  : |f| = Cardinality A -> count (images (elem B) (Cardinality A)) f = 1.
Proof.
  intros H.
  apply dup_free_count.
  -
    apply images_dup_free. apply dup_free_elem.
  -
    rewrite <- H.
    now apply in_images.
Qed.

Lemma images_inner_length (A : discType) (n: nat) :
  forall (xs : list A) ys, ys el (images xs n) -> | ys | = n.
Proof.
  induction n ; intros xs ys ; cbn.
  -
    intros H.
    destruct H ; try tauto.
    now subst ys.
  -
    pattern xs at 1. generalize xs at 2. induction xs as [| x xs] ; cbn.
    +  tauto.
    + intros C E.
      rewrite In_app_iff in E.
      destruct E as [H|H].
      *
        rewrite In_map_iff in H.
        destruct H as [D [H G]]. simpl in *.
        specialize (IHn C D G). subst ys. cbn. omega.
      *
        now apply (IHxs C).
Qed.

Definition extensional_power
           (A B : finType)
           (xs : list (list B))
           (P : xs <<= images (elem B) (Cardinality A))
  : list (A --> B).
Proof.
  revert xs P.
  refine (fix extPow xs P :=  _). destruct xs.
  -  exact nil.
  - apply cons.
    + exists l. specialize (P l (or_introl eq_refl)). unfold pure. dec; auto.
      contradiction ( n (images_inner_length P)).
    +
      eapply extPow. intros ys E. apply P. exact (or_intror E).
Defined.

Lemma vector_extensionality
      (A : finType)
      (B : Type)
      (F G : A --> B) : (image F = image G) -> F = G.
Proof.
  apply subtype_extensionality. 
Qed.

Lemma count_vector_extensionality A B xs P f
  : count (@extensional_power A B xs P) f = count xs (image f).
Proof.
  induction xs as [| x xs].
  -
    reflexivity.
  -
    simpl.
    dec ; rename x into X ; decide (image f = X).
    +
      now rewrite IHxs.
    +
      contradict n.
      now subst f.
    +
      contradict n.
      now apply vector_extensionality.
    +
      apply IHxs.
Qed.

Instance finTypeC_vector (A B : finType) :
  FinTypeC (DiscVect A B).
Proof.
  apply (@Fin_TypeC _ (@extensional_power _ _
                                          (images (elem B) (Cardinality A))
                                          (fun x => fun y => y))).
  intro f.
  rewrite count_vector_extensionality.
  apply vector_enum_sound.
  destruct f as [xs p]. cbn. now impurify p.
Defined.

Canonical Structure FinType_vector (A B : finType) := FinType (DiscVect A B).

Notation "B ^ A" := (FinType_vector A B).

Fixpoint  get_position
          {A : discType}
          (xs : list A) x
  := match xs with
     | [] => 0
     | x' :: xs' => if decision (x = x') then 0
                   else 1 + get_position xs' x
     end.

Definition index {A : finType} (x : A) :=
  get_position (elem A) x.

Notation "# x" := (index x) (at level 65).

Fixpoint get_at (A : Type) (xs : list A)(n: nat) (v : A) : A :=
 match n with
 | 0 =>  match xs with         
       | [] => v                
       | y :: _ => y                       
       end         
 | (S n') => match xs with
              | []  => v
              | _ :: xs' => get_at xs' n' v
              end
 end.

(** application of finite functions *)

Definition apply_vect (A : finType) (B : Type) (f : A --> B) : A -> B.
Proof.
  refine (fun x : A => _).
  destruct (elem A) eqn: E.
  -
    exfalso.
    pose proof (element_In x).
    now rewrite E in H.
  -
    destruct f as [image p].
    destruct image.
    +
      exfalso.
      unfold Card_X_eq, Cardinality in p.
      rewrite E in p. 
      unfolds in p. simpl in *. crush.
    +
      exact (get_at (b :: image0) (# x) b).
Defined.

Coercion apply_vect: vector >-> Funclass.

Definition get_image {A : finType} {B : Type} (f : A -> B) :=
  map f (elem A).

Lemma get_image_in (A B : finType)(f : A -> B)(x : A)
  : (f x) el (get_image f).
Proof.
  unfold get_image. now apply In_map.
Qed.

Lemma get_image_length (A B: finType)(f : A -> B)
  :  |get_image f| = Cardinality A.
Proof.
  apply map_length.
Qed.

Definition vectorise {A B : finType}(f : A -> B) : A --> B :=
  exist (pure (@Card_X_eq A B)) (get_image f) (purify (get_image_length f)).


Lemma get_image_correct (A B : finType)(f : A -> B)
  : get_image f = image (vectorise f).
Proof.
  reflexivity.
Qed.

Lemma help_apply (A B : discType)(xs : list A) (f: A -> B) x y (C: count xs x > 0)
  : get_at (map f xs) (get_position xs x) y = f x.
Proof.
  induction xs as [| x' xs] ; repeat (crush ; dec).
Qed.

Lemma apply_vectorise_inverse (A B : finType)(f : A -> B) (x : A)
  : (vectorise f) x = f x.  
Proof.
 destruct A as [X [A ok]]. destruct A.
 -
   discriminate (ok x).
 -
   cbn  in  *. specialize (ok x). dec.
   +
     congruence.
   +
     apply help_apply.
     omega.
Qed.

Lemma count_number_app
      (A : discType)
      (x : A)
      (xs ys : list A)
      (ok : count (xs ++ x :: ys) x = 1)
  : get_position (xs ++ x :: ys) x = | xs |.
Proof.
  induction xs as [| x' xs].
  -
    cbn.
    now deq x.
  -
    cbn in *.
    dec.
    +
      inverts* ok.
      rewrite count_app in *.
      simpl in *. dec ; crush.
    +
      auto.
Qed.

Lemma get_at_correct (A : discType) (xs ys : list A) y y':
get_at (ys ++ y :: xs) (|ys|) y' = y.
Proof.
  induction ys ; cbn.
  -
    reflexivity.
  -
    cbn in *.
    apply IHys.
Qed.    
    
Lemma right_result
      (A B : finType)
      (x : A)
      (xs xs' : list A)
      (y : B)
      (ys ys' : list B)
      (H : pure (@Card_X_eq A B) (ys' ++ y :: ys))
      (H' : | xs' | = | ys'|)
      (G : elem A = xs' ++ x :: xs)
  : ((exist _ _ H) : A --> B) x = y.
Proof.
  destruct A as [X [C ok]].
  unfold apply_vect.
  cbn in *. subst C.
  destruct xs' ; destruct ys' ; cbn in * ; impurify H ; unfold Card_X_eq in H ;
    cbn in H.
  -
    now deq x.
  -
    rewrite app_length in H.
    inverts H.
    omega.
  -
    rewrite app_length in H.
    cbn in H.
    omega.
  -
    specialize (ok x).
    dec.
    +
      subst d.
      inverts ok.
      rewrite count_app in H1.
      repeat (crush ; dec).
    +
      rewrite count_number_app ; auto.
      inverts H'.
      rewrite H1.
      eapply get_at_correct.
Qed.      

Lemma vectorise_apply_inverse'
      (A B : finType)
      (xs xs' : list A)
      (ys ys' ys'' : list B)
      (H : pure (@Card_X_eq A B) ys'')
      (H' : |ys'| = | xs' |)
      (H'' : |ys| = | xs |)
      (E : ys' ++ ys = ys'') (G : elem A = xs' ++ xs)
  : map ((exist _ _ H) : A --> B) xs = ys.
Proof.
    revert ys ys' xs' H' H'' E G. induction xs ; intros A1 A' B' H' H'' E G.
    -
      cbn.
      symmetry.
      now rewrite <- length_zero_iff_nil.
    -
      cbn.
      destruct A1 ; try (discriminate H''). f_equal.
      +
        subst ys''. simpl in *.
        apply right_result with (xs := xs)(xs' := B')(ys := A1).
        *
          symmetry in H' ; eexact H'. 
        *
          exact G.
      +
        apply (IHxs A1 (A' ++ [d]) (B' ++ [a])).
        *
          repeat rewrite app_length.
          cbn.
          omega.
        *
          now inverts H''.
        *
          now rewrite app_assoc_reverse.
        *
          rewrite G.
          replace (a :: xs) with ([a] ++ xs) by auto.
          now rewrite app_assoc.
Qed.

Lemma vectorise_apply_inverse
      (A B : finType)
      (f : A --> B)
  : vectorise f = f.
Proof.
  apply vector_extensionality. cbn. destruct f as [X p].
  eapply vectorise_apply_inverse'; eauto using app_nil_l ;
  now impurify p.
Qed.
