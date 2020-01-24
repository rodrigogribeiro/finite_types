Set Implicit Arguments.

Require Import
        Discrete.DiscType
        Discrete.Disjoint
        Discrete.DupFree
        Discrete.Filter
        Discrete.In
        Discrete.Inclusion
        Tactics.Tactics.

Import ListNotations.

Section POWER.
  Variable A : discType.
  Context {eq_A_dec : eq_dec A}.

  Fixpoint power (xs : list A) : list (list A) :=
    match xs with
      | nil => [nil]
      | y :: ys => power ys ++ map (cons y) (power ys)
    end.

  Lemma power_incl xs ys :
    xs el power ys -> xs <<= ys.
  Proof.
    revert xs ; induction ys as [ | y ys ] ; simpl ; intros xs D.
    -
      destruct* D as [[]|[]]. 
    - apply In_app_iff in D as [E|E]. now auto.
      apply In_map_iff in E as [zs [E F]]. substs*.
      apply incl_shift ; eauto.
  Qed.

  Lemma power_nil xs :
    nil el power xs.
  Proof.
    induction xs ; simpl ; crush.
    rewrite In_app_iff ; crush.
  Qed.

  Definition rep (xs ys : list A) : list A :=
    filter (fun x => x el xs) ys.

  Lemma rep_incl xs ys :
    rep xs ys <<= xs.
  Proof.
    unfold rep. intros x D. apply In_filter_iff in D. apply D.
  Qed.

  Lemma rep_power xs ys :
    rep xs ys el power ys.
  Proof.
    revert xs. induction ys as [|y ys] ; intros xs.
    -
      simpl ; auto.
    -
      unfold rep ; simpl ;
        decide (y el xs) as [E | E]
        ; rewrite In_app_iff ; specialize (IHys xs) ;
          unfold rep in IHys ; [right ; eauto | left*].
  Qed.

  Lemma rep_in x xs ys :
    xs <<= ys -> x el xs -> x el rep xs ys.
  Proof.
    intros D E. apply In_filter_iff ; crush.
  Qed.
  
  Lemma rep_equiv xs ys :
    xs <<= ys -> rep xs ys === xs.
  Proof.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono xs ys zs :
    xs <<= ys -> rep xs zs <<= rep ys zs.
  Proof.
    intros D.
    apply filter_pq_mono.
    auto.
  Qed.

  Lemma rep_eq' xs ys zs :
    (forall x, x el zs -> (x el xs <-> x el ys)) -> rep xs zs = rep ys zs.
  Proof.
    intros D.
    apply filter_pq_eq.
    auto.
  Qed.

  Lemma rep_eq xs ys zs :
    xs === ys -> rep xs zs = rep ys zs.
  Proof.
    intros D.
    apply filter_pq_eq.
    firstorder.
  Qed.

  Lemma rep_injective xs ys zs :
    xs <<= zs -> ys <<= zs -> rep xs zs = rep ys zs -> xs === ys.
  Proof.
    intros D E F. transitivity (rep xs zs).
    -
      symmetry. apply rep_equiv, D.
    -
      rewrite F. apply rep_equiv, E.
  Qed.

  Lemma rep_idempotent xs ys :
    rep (rep xs ys) ys = rep xs ys.
  Proof.
    unfold rep at 1 3. apply filter_pq_eq.
    intros x D. split.
    +
      apply rep_incl.
    +
      intros E.
      apply In_filter_iff.
      auto.
  Qed.

  Lemma dup_free_power xs :
    dup_free xs -> dup_free (power xs).
  Proof.
    intros D. induction D as [|x U E D]; simpl.
    -
      constructor.
      now auto.
      constructor.
    - apply dup_free_app. 
      + intros [A1 [F G]]. apply In_map_iff in G as [A' [G G']].
        subst A1. apply E. apply (power_incl F). crush.       
      + exact IHD.
      + apply dup_free_map ; congruence.        
  Qed.

  Lemma dup_free_in_power xs ys :
    xs el power ys -> dup_free ys -> dup_free xs.
  Proof.
    intros E D. revert xs E.
    induction D as [|x U D D']; simpl; intros xs E ; crush.
    - apply In_app_iff in E as [E|E] ; crush.
      apply In_map_iff in E as [A' [E E']]. substs.
      constructor.
      *
        intros F; apply D. apply (power_incl E'), F.
      *
        auto.
  Qed.

  Lemma rep_id xs : rep xs xs = xs.
  Proof.
    unfolds.
    apply filter_id. tauto.
  Qed.

  Hint Resolve rep_id.

  Lemma rep_nil ys :
    rep [] ys = [].
  Proof.
    unfolds ; induction ys ; crush.
    decide (False) ; crush.
  Qed.

  Hint Resolve rep_nil.
    
  Lemma rep_dup_free xs ys :
    dup_free ys -> xs el power ys -> rep xs ys = xs.
  Proof.
    intros D ; revert xs.
    induction D as [|x U E F] ; intros xs G.
    - 
      destruct* G as [[]|[]].
    -
      simpl in G.
      apply In_app_iff in G as [G|G].
      +
        simpl.
        decide (x el xs) as [H|H].
        *
          exfalso.
          apply E.
          apply (power_incl G), H.
        * 
          unfolds.
          rewrite filter_fst' ; auto.
          specialize (IHF _ G). crush.
      +
        apply In_map_iff in G as [A' [G H]]. subst xs.
        unfold rep. simpl.
        decide (x = x \/ x el A') as [G|G] ; crush. 
        *
          f_equal. specialize (IHF A' H). unfold rep in IHF. rewrite <- IHF at -2.
          apply filter_pq_eq. apply power_incl in H.
          intros z K. split; [|now auto].
          intros [L|L]; subst; tauto.
        *
          exfalso. apply E. apply power_incl in H. eauto.
  Qed.  

  Lemma power_extensional xs ys zs :
    dup_free zs -> xs el power zs -> ys el power zs -> xs === ys -> xs = ys.
  Proof.
    intros D E F G.
    rewrite <- (rep_dup_free D E). rewrite <- (rep_dup_free D F).
    apply rep_eq, G.
  Qed.

End POWER.