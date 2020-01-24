Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.
Set Contextual Implicit.

Require Import
        List 
        Finite.FiniteType
        Tactics.Tactics.

Import ListNotations.


(** definition of a DFA *)

Section DFA.
  Variable sigma : finType.

  Definition word := list sigma.
  Definition epsilon : word := (@nil sigma).

  Record dfa : Type
    := DFA { 
        S :> finType      (** state set      *)
      ; s : S             (** starting state *)
      ; F : dec_pred S    (** final state predicate *)
      ; d : S -> sigma -> S (** transition function *)
      }.

  Section ACCEPT.
    Variable M : dfa.

  (** extended transition function *)

    Fixpoint d_star (q : M)(w : word) :=
      match w with 
      | [] => q
      | c :: w' => d_star (d q c) w'
      end.

    Definition accept (w : word) := F (@d_star s w).

    Instance accept_dec w : dec (accept w).
    Proof.
      auto.
    Defined.

    Inductive reach (q : M) : M -> Prop :=
    | Refl : reach q q
    | Step q' c : reach (d q c) q' -> reach q q'.

    Hint Constructors reach.

    Definition reach_with q w q' := d_star q w = q'.

    Lemma reach_is_reach_with (q q' : M) : reach q q' <-> exists w, reach_with q w q'.
    Proof.
      split.
      +
        intros H ; induction H ; crush.
        -
          now exists epsilon.
        - 
          exists (c :: x) ; crush.
      +
        intros [w H]. revert q H ; induction w ; intros q H ; crush.
        -
          econstructor 2.
          apply IHw.
          apply H.
    Qed.

    Hint Resolve reach_is_reach_with.

    Lemma reach_transitive (q : M ) q' q'': reach q q' /\ reach q' q'' -> reach q q''.
    Proof.
      intros [R R']. induction R ; eauto.
    Qed.

    Lemma reach_d_star q w: reach q (d_star q w).
    Proof.
      apply reach_is_reach_with. now exists w.
    Qed.

    Definition step_reach (states : list M)(q : M)
      := exists q' x, q' el states /\ reach_with q' [x] q.

    Lemma step_reach_consistent: step_consistent step_reach.
    Proof.
      intros B q H B' sub.
      destruct H as [q' [x [E R]]].
      exists* q' x. 
    Qed.    

    Definition reachable_states (q : M) := finite_iter step_reach [q].

    Lemma reachable_states_least_fp q
      : least_fp_containing (finite_iter_step step_reach)
                            (reachable_states q) [q].
    Proof.
      apply step_consistent_least_fp.
      apply step_reach_consistent.
    Qed.

    Lemma reachable_states_correct1 (q : M) : inclp (reachable_states q) (reach q).
    Proof.
      apply finite_iter_ind.
      -
        intros x ; crush.
      -
        intros set q' H [q'' [x [E H1]]] ; eapply reach_transitive ; split.
        +
          apply (H _ E).
        +
          apply reach_is_reach_with.
          exists* [x].
    Qed.

    Lemma reachable_states_correct2' q q' : q' el reachable_states q ->
                                 forall q'', reach q' q'' -> q'' el reachable_states q.
    Proof.
      intros E q'' H ; induction H ; crush.
      -
        apply IHreach. apply closure_finite_iter. now exists* q0 c.
    Qed.

    Lemma reachable_states_correct2 q: forall q', reach q q' -> q' el reachable_states q.
    Proof.
      apply reachable_states_correct2'. apply preservation_finite_iter ; crush.
    Qed.        

    Lemma reachable_states_correct q q' : reach q q' <-> q' el (reachable_states q).
    Proof.
      split ; [ apply reachable_states_correct2
              | apply reachable_states_correct1].
    Qed.

    Global Instance reach_dec q q': dec (reach q q').
    Proof.
      eapply dec_prop_iff.
      -
        symmetry. apply reachable_states_correct.
      - auto.
    Qed.    

    Global Instance reach_with_something_dec q q' : dec (exists w, reach_with q w q').
    Proof.
      apply dec_prop_iff with (X := reach q q') ; eauto.
    Qed.

    Lemma reachable_states_reach_with q q'
      : (exists w, reach_with q w q') <-> q' el reachable_states q.
    Proof.
      rewrite <- reach_is_reach_with.  apply reachable_states_correct.
    Qed.

    Lemma d_star_reachable_states w q : d_star q w el (reachable_states q).
    Proof.
      apply reachable_states_reach_with. now exists w.
    Qed.

    Notation in_lang w := (accept w) (only parsing).

    (** accepting all words in sigma* *)

    Lemma accepts_sigma_star_if_all_states_final
      : (forall w, in_lang w) <-> forall q : M, q el (reachable_states s) -> F q.
    Proof.
      split.
      -
        intros H q Hel.
        rewrite <- reachable_states_reach_with in Hel.
        destruct Hel as [w Hw]. unfolds in Hw.
        rewrite <- Hw. apply (H w).
      -
        intros H w. apply (H (d_star s w)). apply d_star_reachable_states.
    Qed.

    Global Instance accepts_sigma_star_dec : dec (forall w, in_lang w).
    Proof.
      decide( forall q, q el reachable_states s -> F q) as [H | H].
      - left. now apply accepts_sigma_star_if_all_states_final.
      - right. now rewrite accepts_sigma_star_if_all_states_final.
    Defined.

    (** rejecting all words, empty language *)

    Definition empty := forall w, ~ in_lang w.

    Definition negate_final_states := DecPred (fun x => ~ (@F M x)).

    Definition complement := DFA s negate_final_states (@d M).
  End ACCEPT.

  Notation in_lang A w := (accept A w) (only parsing).

  Section OPERATIONS.
    Variable M : dfa.

    Lemma complement_correct w : accept (complement M) w <-> ~ (accept M w).
    Proof.
      splits*.
    Qed.

    Global Instance empty_dec : dec (empty M).
    Proof.
      apply (dec_trans (@accepts_sigma_star_dec (complement M))).
      now setoid_rewrite complement_correct.
    Qed.

    Lemma empty_reachable_states
      : empty M <-> forall (q : M), q el (reachable_states s) -> ~ (F q).
    Proof.
      split.
      - intros empt q E F . rewrite <- reachable_states_reach_with in E.
        destruct E as [w R].
        specialize (empt w). apply empt. unfold accept. now rewrite R.
      - intros H w acc. specialize (H (d_star s w)). apply H.
        + apply d_star_reachable_states.
        + exact acc.
    Qed.

    Instance exists_accept_dec: dec (exists w, accept M w).
    Proof.
      decide (empty M) as [H | H].
      - firstorder.
      - left. unfold empty in H.  rewrite empty_reachable_states in H.
        rewrite DM_notAll in H.
        + destruct H as [q H]. destruct (dec_DM_impl _ _ H) as [H' acc].
          rewrite <- reachable_states_reach_with in H'.
          destruct H' as [w R]. exists w.  rewrite <- R in acc.
          apply dec_DN; auto.     
        + auto.
    Qed.

    Instance exists_not_accept_dec : dec (exists w, ~ accept M w).
    Proof.
      decide (forall w, accept M w) as [H | H].
      - right. firstorder.
      - left. rewrite accepts_sigma_star_if_all_states_final in H.
        rewrite DM_notAll in H.
        + destruct H as [q H].  destruct (dec_DM_impl _ _ H) as [H' acc].
          rewrite <- reachable_states_reach_with in H'.
          destruct H' as [w R]. exists w.  now rewrite <- R in acc.
        + auto.
    Qed.      
End OPERATIONS.

    (** DFA recognizing epsilon *)

Definition Epsilon_autom : dfa.
Proof.
  refine (DFA (inl tt)
              (DecPred (fun q: unit + unit => if q then True else False))
              (fun _ _ => inr tt)).
  intros [[]|[]]; auto.
Defined.

Lemma inr_fix_epsilon w : (@d_star Epsilon_autom (inr tt) w) = inr tt.
Proof.
  now induction w.
Qed.

Lemma Epsilon_autom_correct w: accept Epsilon_autom w <-> w = nil.
Proof.
  split.
  - cbn. destruct w.
    + reflexivity.
    + cbn. now rewrite inr_fix_epsilon.
  - intros H. subst w. cbn. exact I.
Qed.

(** DFA for a symbol x *)

Definition F_cons (M : dfa) (q : option M + unit) :=
  match q with
  | inl None => False
  | inl (Some q) => F q
  | inr tt => False
  end.
    
Definition d_cons x (M : dfa)
           (q : option M + unit) y  :=
  match q with
  | inl None => if decision (y = x) then inl (Some s) else inr tt
  | inl (Some q) => inl (Some (d q y))
  | inr tt => inr tt
  end.

Instance F_cons_dec  (M : dfa) (q : option M + unit) : dec (F_cons q).
Proof.
  destruct q.
  - destruct o ; auto.
  - destruct u ; auto.
Qed.

Definition cons (M : dfa) (x : sigma) :=
  DFA (inl None) (DecPred (@F_cons M)) (@d_cons x M).

Lemma inr_fix M x w : (@d_star (cons M x) (inr tt) w) = inr tt.
Proof.
  now induction w.
Qed.

Lemma cons_correct  (M : dfa) x w : accept M w <-> accept (cons M x) (x::w).
Proof.
  cbn in *. deq x. unfold accept. generalize (@s M).  induction w; firstorder.
Qed.

(** word automata *)

Fixpoint word_dfa (w : word) : dfa :=
  match w with
  | [] => Epsilon_autom
  | x :: xs => cons (word_dfa xs) x
  end.

Lemma word_dfa_correct : forall w, accept (word_dfa w) w.
Proof.
  induction w ; try now auto.
  -
    simpl.
    now rewrite <- cons_correct.
Qed.


End DFA.