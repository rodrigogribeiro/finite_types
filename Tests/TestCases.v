Require Import
        List
        Discrete.Count
        Discrete.DiscType.

Import ListNotations.

(** test case *)

Example test_count_bool : count [true ; false] true = 1.
Proof.
  reflexivity.
Qed.
