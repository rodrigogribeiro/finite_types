Set Implicit Arguments.

Require Import
        Discrete.DiscreteType
        Finite.FinType
        Tactics.Tactics.

Import ListNotations.


Lemma option_enum_sound (A : finType) x :
  count (to_option_list (elem A)) x = 1.
Proof.
  destruct x.
  +
    rewrite count_option_list. apply enum_sound.
  +
    apply count_option_list_none.
Qed.

Instance FinTypeC_Option(A : finType): FinTypeC (?? A).
Proof.
  econstructor.  apply option_enum_sound.
Defined.

Canonical Structure FinType_Option (A : finType) := FinType (?? A).

Notation " ? F" := (FinType_Option F) (at level 39).

Lemma cardinality_option (A : finType) : Cardinality (? A) = 1 + (Cardinality A).
Proof.
  cbn. now rewrite map_length.
Qed.