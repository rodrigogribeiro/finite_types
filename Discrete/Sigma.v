Set Implicit Arguments.

Require Import
        Discrete.DiscType.

Import Logic.EqdepFacts.

(** definition of pure predicates and related lemmas *)

Definition pure {A : Type}(p : A -> Prop){D : forall x, dec (p x)} x :=
  if decision (p x) then True else False.

Arguments pure {A} p {D} x.


Lemma pure_equiv {A : Type}(p : A -> Prop) {D : forall (x : A), dec (p x)}(x : A)
  : p x <-> (pure p x).
Proof.
  unfold pure. now dec.
Qed.

Lemma pure_impure  (P: Prop) {D : dec P} (norm: if decision (P) then True else False) : P.
Proof.
  dec ; tauto.
Qed.

Ltac impurify H :=
  pose proof (pure_impure H) as impureH ;
  try (clear H ; rename impureH into H).

Lemma purify (X: Type) (p: X -> Prop) (D:forall x, dec (p x)) x (px: p x): pure p x.
Proof.
  now apply pure_equiv.
Qed.

Arguments purify {X} {p} {D} {x} px.

Lemma pure_eq (A : Type) (p : A -> Prop) (D : forall x, dec (p x)) x (p1 p2 : pure p x)
  : p1 = p2.
Proof.
  unfold pure in *. dec.
  +
    now destruct p1, p2.
  +
    contradiction p1.
Qed.

(** subtype definition and some lemmas *)

Definition subtype {A : Type} (p : A -> Prop) {D: forall x, dec (p x)} := {x : A | pure p x}.
Arguments subtype {A} p {D}.

Lemma subtype_extensionality
      (A : Type) (p : A -> Prop)
      {D : forall x, dec (p x)} (x x': subtype p) : proj1_sig x = proj1_sig x' <-> x = x'.
Proof.
  splits ; crush.
  -
    destruct x, x'. cbn in H. subst x0. f_equal. apply pure_eq.
Qed.


(** lemmas about dependent products *)

Lemma sigT_proj1_fun (A : discType) (f : A -> Type) (x x' : A) (y : f x) (y' : f x')
  : existT f x y = existT f x' y' -> x = x'.
Proof.
 crush.
Qed.

Instance subtype_eq_dec
         (A : discType)
         (p : A -> Prop)
         (_ : forall x, dec (p x)) : eq_dec (subtype p).
Proof.
  intros y z. destruct y as [x p1], z as  [x' p2]. decide (x = x').
  -
    left.  now apply subtype_extensionality.
  -
    right. intro H. apply n. apply (eq_funTrans (@proj1_sig _ (pure p)) H).
Qed.    

Lemma sigT_proj2_fun
      (A : discType)(f : A -> Type)
      (E : forall x, eq_dec (f x))
      (x : A) (y y': f x)
  : existT f x y = existT f x y' -> y = y'.
Proof.
  intro H.
  rewrite <- (eq_sigT_snd H).
  now rewrite (Hedberg (eq_sigT_fst H) (eq_refl x)).
Qed.

Instance eq_dec_sigT
         (A : discType) (f : A -> Type) (E : forall x, eq_dec (f x))
  : eq_dec (sigT f).
Proof.
  intros p1 p2.
  destruct p1, p2. decide (x = x0).
  -
    subst x0. decide (f0 = f1).
    +
      left ; crush.
    +
      right. intro eq. apply n. now apply sigT_proj2_fun.
  -
    right.
    intro H.
    apply n.
    apply (eq_funTrans (@projT1 _  f) H).
Qed.


(** cannonical structure for dependent products *)

Canonical Structure DiscSigT
          (A : discType)
          (f : A -> Type) {D: forall x, eq_dec (f x)} := DiscType (sigT f).
Arguments DiscSigT {A} f {D}.


(** cannonical structure for subtypes *)

Canonical Structure DiscSubtype
          (A : discType)
          (p : A -> Prop)
          (D: forall x, dec (p x)) := DiscType (subtype p).
Arguments DiscSubtype {A} p {D}.
