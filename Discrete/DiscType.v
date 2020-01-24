Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.

Set Implicit Arguments.

Hint Extern 4 => exact _.

Require Export
        Arith_base
        List
        Tactics.Tactics
        Setoid
        Morphisms.

(** basic stuff *)

Lemma neg_or A B: ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  tauto.
Qed.

Lemma DM_not_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.


Ltac sum_solver :=
  try solve [left ; congruence] ;
  try solve [right ; congruence].

(** definition of a type class for decidable
    predicates *)

Definition dec (P : Prop) : Type := {P} + {~ P}.

Notation "'eq_dec' A" := (forall x y : A, dec (x = y))(at level 70).

Existing Class dec.

Definition decision (P : Prop){D : dec P} : dec P := D.
Arguments decision P {D}.

Ltac dec := repeat (destruct decision).

Ltac deq x := destruct (decision (x=x)) as [[]  | isnotequal] ;
              [> | contradict isnotequal; reflexivity] .

Tactic Notation "decide" constr(p) := 
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.

(** coercion from Prop to bool *)

Coercion toBool (P: Prop) (D: dec P) := if decision P then true else false.
Arguments toBool P {D}.


Definition injective (A B : Type) (f : A -> B):= forall x y, f x = f y -> x = y.
Definition surjective (A B : Type) (f : A -> B) : Prop := forall y, exists x, f x = y.
Definition bijective (A B : Type) (f : A -> B): Prop := injective f /\ surjective f.

Lemma injective_apply (A B : Type) (f : A -> B) (x y : A) :
  injective f -> f x = f y -> x = y.
Proof.
  auto.
Qed.

Lemma surjective_apply (A B : Type) (f : A -> B) (x y : A) :
  surjective f -> forall y, exists x, f x = y.
Proof.
  auto.
Qed.


Lemma loop (A B : Type) (f : A -> B) (g : B -> A)
  : (forall x, g (f x) = x) -> injective f.
Proof.
  intro H. unfold injective. intros x  y G.
  pose proof (H x) as H'. specialize (H y).
  rewrite G in H'.
     subst x. exact H.
Qed.

(** improving automation *)

Hint Extern 4 => 
    match goal with
    | [ |- dec ?p ] => exact (decision p)
    end.

Hint Extern 4 =>
    match goal with
    | [ |- dec ((fun _ => _) _) ] => simpl
    end : typeclass_instances.

(** basic instances for decidabitity *)

Fact dec_trans P Q :
  dec P -> P <-> Q -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance True_dec :
  dec True.
Proof. 
  unfold dec ; auto. 
Qed.

Instance False_dec :
  dec False.
Proof. 
  unfold dec ; auto. 
Qed.

Instance impl_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X -> Y).
Proof.
  unfold dec ; tauto.
Defined.

Instance and_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X /\ Y).
Proof.
  unfold dec ; tauto.
Defined.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof.
  unfold dec ; tauto.
Defined.

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof.
  unfold not. auto.
Defined.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof.
  unfold iff. auto.
Qed.

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof.
  unfold dec ; tauto.
Qed.

Lemma dec_DM_and X Y : 
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof.
  unfold dec ; tauto.
Qed.

Lemma dec_DM_impl X Y : 
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof.
  unfold dec ; tauto.
Qed.

Lemma dec_prop_iff (X Y : Prop) : 
  (X <-> Y) -> dec X -> dec Y.
Proof.
  unfold dec ; tauto.
Defined.

Instance unit_eq_dec : eq_dec unit.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  tauto.
Qed.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x, y. left*.
Qed.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros x  ; destruct x.
Qed.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  intros D. apply list_eq_dec. exact D. 
Qed.

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

Instance prod_eq_dec (T1 T2 : Type) (E1 : eq_dec T1) (E2 : eq_dec T2):
  eq_dec (T1 * T2).
Proof.
  intros. unfold dec.  destruct x, y.
  decide (t = t1) ; decide (t0 = t2) ; sum_solver.
Qed.

Instance option_eq_dec (X : Type) (e : eq_dec X) :
  eq_dec (option X).
Proof.
  intros. destruct x, y ; sum_solver.
  +
    decide (x = x0) ; sum_solver.
Qed.

Instance sum_eq_dec (X : Type) (Y : Type) (ex : eq_dec X) (ey : eq_dec Y):
  eq_dec (sum X Y).
Proof.
  intros. destruct x, y ; sum_solver.
  -
    decide (x = x0) ; sum_solver.
  -
    decide (y0 = y) ; sum_solver.
Qed.

Structure discType
  := DiscType {
        disctype :> Type
     ;  decide_eq : eq_dec disctype 
     }.

Arguments DiscType disctype {decide_eq}.
Existing Instance decide_eq.

Definition toDiscType (A : Type) {D : eq_dec A} : discType := DiscType A.
Arguments toDiscType A {D}. 

Lemma toDiscTypeCorrect (T : discType) : T = toDiscType T.
Proof.
  destruct* T.
Qed.

Lemma Hedberg (A : discType) (x y : A) (E E' : x = y) : E = E'.
Proof.
  pose (f := fun y : A => fun E: x = y => match (decision (x = y)) with
                                   | left b => b
                                   | _ => E end).
  apply (@injective_apply _ _(f y) E E'). 
  -
    pose (join := fun (y z : A) (e : x = y) => eq_trans (z := z) (eq_sym e)).
    apply  (@loop _ _ (f y)  (join x y (f x (eq_refl x)))).
    intros []. unfold f. now deq x.
  -
    unfold f.  decide (x = y); tauto.
Qed.

Require Import Logic.EqdepFacts.

Theorem Streicher_K (A : discType) (x : A) (P : x = x -> Prop)
  : P (eq_refl x) ->  forall p, P p.
Proof.
  intros H p. now rewrite (Hedberg p (eq_refl x)).
Qed.

Lemma dec_refl (A : discType) (x : A)
  : decision (x = x) = left eq_refl.
Proof.
  dec.
  -  f_equal.  now apply (@Streicher_K _ _  (fun e => e = eq_refl x) ).
  - congruence.
Qed.

Hint Resolve dec_refl.

Lemma eq_funTrans (X Y : Type) (f: X -> Y) (x x': X): x = x' -> f x = f x'.
Proof.
  crush.
Qed.

Canonical Structure DiscUnit := DiscType unit.
Canonical Structure DiscBool := DiscType bool.
Canonical Structure DiscNat := DiscType nat.
Canonical Structure DiscOption (T : discType)  := DiscType (option T).
Canonical Structure DiscProd (T1 T2 : discType) := DiscType (T1 * T2).
Canonical Structure DiscEmpty_set := DiscType Empty_set.
Canonical Structure DiscSum (X Y : discType) := DiscType (X + Y).
Canonical Structure DiscList (X : discType) := DiscType (list X).
Canonical Structure DiscFalse := DiscType False.
Canonical Structure DiscTrue := DiscType True.


Reserved Notation "T1 ** T2" (at level 69, no associativity).
Bind Scope DiscTypeScope with discType.
Notation "T1 ** T2" := (DiscProd T1 T2) : DiscTypeScope.
Notation "T1 ** T2" := (DiscProd (toDiscType T1) (toDiscType T2)).
Notation " ?? F" := (DiscOption F) (at level 65).

(** decidable predicates and relations *)

Structure dec_pred A
  := DecPred {
         predicate :> A -> Prop;
         decide_pred x : dec (predicate x)
     }.

Arguments DecPred {A} predicate {decide_pred}.

Existing Instance decide_pred.
  
Instance pred_dec A (p : dec_pred A) x :
  dec (p x).
Proof.
  apply decide_pred.
Qed.

Structure dec_relation A
  := DecRel {
         relation :> A -> A -> Prop;
         decide_rel x y : dec (relation x y)
     }.

Arguments DecRel {A} relation {decide_rel}.

Instance dec_relation_dec A (R : dec_relation A) x y :
  dec (R x y).
Proof.
  apply decide_rel.
Qed.

Lemma dec_DM_and' X Y :  
  dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_all X (p : X -> Prop) (D : forall x, dec (p x)):
  (forall x, p x) <-> ~ exists x, ~ p x.
Proof.
  firstorder.
Qed.
