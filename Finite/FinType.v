Set Implicit Arguments.

Require Export
        Discrete.DiscreteType
        Tactics.Tactics.


Import ListNotations.

Class FinTypeC (type : discType) : Type
  := Fin_TypeC {
         enum : list type
       ; enum_sound : forall v : type, count enum v = 1              
       }.

Structure finType : Type
  := FinType {
       type :> discType
     ; class : FinTypeC type
     }.

Arguments FinType type {class}.
Existing Instance class | 0.

Instance FinTypeClass2 (F: finType) :FinTypeC (toDiscType F) | 1.
Proof.
 now destruct F as [[type eqdec] class].
Defined.

Definition toFinType (T: Type) (_: eq_dec T)  (f: FinTypeC _): finType
  := FinType (toDiscType T).
Arguments toFinType T {_} {f}.

Lemma toFinType_sound (A : Type) {H: eq_dec A} {f: FinTypeC (toDiscType A)}
  : A = toFinType A.
Proof.
  reflexivity.
Qed.

Lemma toFinType_idempotent (A : finType) : toFinType (toFinType A) = toFinType A.
Proof.
  reflexivity. 
Qed.

Definition elem (F: finType) := @enum (type F) (class F).
Hint Unfold elem.
Hint Unfold class.

Lemma element_In (A : finType) (x : A) : x el (elem A).
Proof.
  rewrite count_in_gt_zero.
  pose proof (enum_sound x) as H. unfold elem. omega.
Qed.


Hint Resolve element_In.
Hint Resolve enum_sound.


Lemma all_incl (A : finType) (xs : list A) : xs <<= elem A.
Proof.
  intros x _. apply element_In.
Qed.

Arguments all_incl {A} xs.
Hint Resolve all_incl.

Theorem Equivalence_property_all (A : finType) (p: A -> Prop) :
  (forall x, p x) <-> forall x, x el (elem A) -> p x.
Proof.
  splits*.  
Qed.

Theorem Equivalence_property_exists (A : finType) (p : A -> Prop):
  (exists x, p x) <-> exists x, x el (elem A) /\ p x.
Proof.
  splits*.
Qed.

Theorem Equivalence_property_exists' (A : finType) (p: A -> Prop):
    (exists x, p x) <-> exists x, x el (elem A) -> p x.
Proof.
  splits*.
Qed.


Instance finType_forall_dec
         (A : finType)
         (p : A -> Prop)
  : (forall x, dec (p x)) -> dec (forall x, p x).
Proof.
  intros D. apply dec_trans with (P := forall x, x el (elem A) -> p x) ; auto. 
  - rewrite (Equivalence_property_all p) ; tauto.
Qed.

Instance finType_exists_dec (A : finType) (p : A -> Prop)
  : (forall x, dec (p x)) -> dec (exists x, p x).
Proof.
  intros D.
  apply dec_trans with (P := exists x : A, x el (elem A) /\ p x) ; auto.
  rewrite (Equivalence_property_exists p) ; tauto.
Qed.

Definition finType_cc (A : finType) (p : A -> Prop) (D : forall x, dec (p x))
  : (exists x, p x) -> {x | p x}.
Proof.
  intro H.
  assert(exists x, x el (elem A) /\ p x) as E by firstorder.
  pose proof (list_cc D E) as [x G].
  now exists x.
Defined.

Definition pickx (A : finType) : A + (A -> False).
Proof.
  destruct A as [X [enum ok]]. induction enum ; try tauto.
  -
    right.
    intro x.
    discriminate (ok x).
Defined.

Lemma DM_notAll (A : finType) (p : A -> Prop) (D : forall x, dec (p x))
  : (~ (forall x, p x)) <-> exists x, ~ (p x).
Proof.     
  decide (exists x,~ p x); firstorder.
Qed.

Lemma DM_exists (A : finType) (p : A -> Prop) (D: forall x, dec (p x)):
  (exists x, p x) <->  ~(forall x, ~ p x).
Proof.
  splits*.
  - decide (exists x, p x); firstorder.
Qed.    

Lemma bool_enum_sound x :
  count [true; false] x = 1.
Proof.
  simpl.
  decide (x = true) ; destruct x ; substs ; simpl in * ; try congruence.
Qed.

Lemma unit_enum_sound x :
  count [tt] x = 1.
Proof.
  simpl. destruct x ; decide (tt = tt) ; congruence.
Qed.

Lemma Empty_set_enum_sound (x : Empty_set) :
  count nil x = 1.
Proof.
  tauto.
Qed.

Lemma True_enum_sound x :
  count [I] x = 1.
Proof.
  simpl; dec;  destruct x; congruence.
Qed.

Lemma False_enum_sound (x : False):
  count nil x = 1.
Proof.
  tauto.
Qed.

Instance finTypeC_bool : FinTypeC DiscBool.
Proof.
  econstructor. apply bool_enum_sound.
Defined.

Instance finTypeC_unit: FinTypeC DiscUnit.
Proof.
  econstructor. apply unit_enum_sound.
Defined.

Instance finTypeC_empty : FinTypeC DiscEmpty_set.
Proof.
  econstructor. apply Empty_set_enum_sound.
Defined.

Instance finTypeC_True : FinTypeC DiscTrue.
Proof.
  econstructor. apply True_enum_sound.
Defined.

Instance  finTypeC_False : FinTypeC DiscFalse.
Proof.
  econstructor. apply False_enum_sound.
Defined.

Definition FinType_unit : finType := FinType DiscUnit.
Definition FinType_bool: finType :=  FinType DiscBool.
Definition FinType_Empty_set :finType := FinType DiscEmpty_set.
Definition FinType_True : finType := FinType DiscTrue.
Definition FinType_False : finType :=  FinType DiscFalse.

Canonical Structure FinType_unit.
Canonical Structure FinType_bool.
Canonical Structure FinType_Empty_set.
Canonical Structure FinType_True.
Canonical Structure FinType_False.

Definition Cardinality (A : finType) := | elem A |.
