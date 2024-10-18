(* Require Import List.
Import ListNotations. *)

Require Export Basic.










(*****could not solve*****)

Inductive repeats {A : Type} : list A -> Prop :=
  | repeats_here : forall x l,
    In x l -> repeats (x :: l)
  | repeats_later : forall x l, 
    repeats l -> repeats (x :: l).


Definition excluded_middle : Prop := forall P, P \/ ~P.

Check excluded_middle.

Lemma pigeonhole_principle: excluded_middle ->
  forall (A : Type) (l1 l2 : list A),
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
      repeats l1.

      Proof.
        intros EM X l1. induction l1 as [|x l1' IHl1'].
        - (* l1 = [] *)
          simpl. intros. inversion H0.
        - (* l1 = x :: l1' *)
          simpl. intros l2 HIn Hlen. destruct l2 as [|y l2'].
          + (* l2 = [] *)
            intros. simpl in Hlen. exfalso. apply (HIn x). left. reflexivity.
          + (* l2 = y :: l2' *)
            destruct (EM (In x l1')) as [EmInT | EmInF].
            * (* In x l1' *)
              apply repeats_here. apply EmInT.
            * (* ~ In x l1' *) 
              destruct (in_split _ x (y::l2')) as [la [lb Eyl2]].
              -- (* must prove [In x (y :: l2')] to get equation below *) 
                 apply (HIn x). left. reflexivity.
              -- (* Eyl2: y :: l2' = la ++ x :: lb *)
                 apply repeats_later. apply (IHl1' (la++lb)).
                 ++ (* must prove [In x l1' -> In x l2] where [l2 = la ++ lb] *)
                    intros z HInz. rewrite Eyl2 in HIn.
                    (* assertion is important below *)
                    assert (Neqx : x <> z).
                    { unfold not in HInz. unfold not. intros Exz. rewrite Exz in EmInF.
                      apply EmInF. apply HInz. }
                    (* need to show this implication when [x <> z] so we can apply later *)
                    assert (In_split_Neqx: In z (la ++ x :: lb) -> In z (la ++ lb)).
                    { intros In_unsplit. apply In_app_iff. apply In_app_iff in In_unsplit.
                      destruct In_unsplit as [Iu | Iu].
                      left. apply Iu. right. simpl in Iu. destruct Iu as [Eqx | In_lb].
                      exfalso. apply Neqx, Eqx.
                      apply In_lb. }
                    apply In_split_Neqx. apply HIn. right. apply HInz.
                 ++ (* must prove [length l2 < length l1'] where [l2 = la ++ lb] *)
                    rewrite Eyl2 in Hlen.
                    rewrite app_length in Hlen. simpl in Hlen. rewrite <- plus_n_Sm in Hlen.
                    apply -> leSBoth in Hlen. unfold lt. rewrite app_length. apply Hlen.
      Qed.
Proof.
  intros EM.
  intros A l1.
  induction l1 as [| x l1' IHl1']
    ; intros l2 H1 H2.
  - simpl in H2.
    inversion H2.
  - change (forall y : A, In y (x :: l1') -> In y l2) in H1.
    assert (H4 : In x l2).
      { apply H1.
        simpl.
        left.
        reflexivity. }
    pose proof (IHl1' (x :: l1')) as H5.
    assert (H6 : forall x : A, In x l1' -> In x (x :: l1')).
      { intros x0 H6_1. unfold In in H6_1. simpl. left. reflexivity. }
    assert (H7 : forall x : A, In x l1' -> In x (x :: l1')).
      { intros x0 H7_1. simpl. right. apply H7_1. }
    pose proof (H1 x) as H8.
    (* remember (x :: l1') as l2' eqn:Heq1. *)
    assert (H3 : In x l1' \/ ~In x l1').
      { apply EM. }
    destruct H3 as [H3_1 | H3_2].
    + apply repeats_here.
      assumption.
    + defered. apply repeats_here.
     assert (H4 : In x l2).
        { apply H1. }
      pose proof (in_split A x l2 H4) as H5.
      destruct H5 as [l3 [l4 H5]].
      pose proof (IHl1' (l3 ++ l4)) as H6.
      assert (H7 : forall x0 : A, In x0 l1' -> In x0 (l3 ++ l4)).
        { intros x0 H7_1.
          assert (H7_2 : In x0 l2).
            { apply H1. }
          rewrite H5 in H7_2.
          apply in_app_iff.
          apply in_app_iff in H7_2.
          destruct H7_2 as [H7_2_1 | H7_2_2].
          - left.
            apply H7_2_1.
          - right.
            apply H7_2_2. }
      apply H6 in H7.
      apply H7.
      assert (H8 : length (l3 ++ l4) < length (x :: l1')).
        { rewrite H5.
          rewrite app_length.
          simpl.
          rewrite plus_comm.
          simpl.
          rewrite plus_comm.
          simpl.
          apply Lt.lt_n_S.
          apply H2. }
      apply H8.
    
    
    
    
    
    
    apply H3_2 in H4.
      assert (H9 : In x l1').
        { apply H7. }
      pose proof (in_split A x l2 H4) as H10.
      destruct H10 as [l3 [l4 H10]].
      pose proof (IHl1' (l3 ++ l4)) as H11.
      assert (H12 : forall x0 : A, In x0 l1' -> In x0 (l3 ++ l4)).
        { intros x0 H12_1.
          assert (H12_2 : In x0 l2).
            { apply H1. }
          rewrite H10 in H12_2.
          apply in_app_iff.
          apply in_app_iff in H12_2.
          destruct H12_2 as [H12_2_1 | H12_2_2].
          - left.
            apply H12_2_1.
          - right.
            apply H12_2_2. }
      apply H11 in H12.
      apply H12.
      assert (H13 : length (l3 ++ l4) < length (x :: l1')).
        { rewrite H10.
          rewrite app_length.
          simpl.
          rewrite plus_comm.
          simpl.
          rewrite plus_comm.
          simpl.
          apply Lt.lt_n_S.
          apply H2. }
      apply H13.
     apply repeats_later.
      exfalso. assert (H4 : In x l2).
      { apply H1.
        simpl.
        left.
        reflexivity. }
      apply repeats_here.
      exfalso.
      
      induction l1' as [| x' l1'' IHl1''].
      * unfold In.

      
      pose proof (in_split A x l2 H4) as H5.
      destruct H5 as [l3 [l4 H5]].
      pose proof (IHl1' (l3 ++ l4)) as H6.
      inversion H4.
     apply repeats_here.
      apply H3_2.
      contradiction.
    
    pose proof (IHl1' (x :: l1')) as H4.
      assert (H5 : length l2 < length (x :: l1')).
        { simpl.
          apply H2. }
      apply H4 in H5.
      apply repeats_later.
      apply H5.
     apply repeats_later.


    destruct H3 as [H3_1 | H3_2].
    + apply repeats_here.
      assumption.
    + apply repeats_here.
      contradiction.

    assert (H4 : In x l2).
        { apply H1. }
      pose proof (in_split A x l2 H4) as H5.
      destruct H5 as [l3 [l4 H5]].
      pose proof (IHl1' (l3 ++ l4)) as H6.
      assert (H7 : forall x0 : A, In x0 l1' -> In x0 (l3 ++ l4)).
        { intros x0 H7_1.
          assert (H7_2 : In x0 l2).
            { apply H1. }
          rewrite H5 in H7_2.
          apply in_app_iff.
          apply in_app_iff in H7_2.
          destruct H7_2 as [H7_2_1 | H7_2_2].
          - left.
            apply H7_2_1.
          - right.
            apply H7_2_2. }
      apply H6 in H7.
      apply H7.
      assert (H8 : length (l3 ++ l4) < length (x :: l1')).
        { rewrite H5.
          rewrite app_length.
          simpl.
          rewrite plus_comm.
          simpl.
          rewrite plus_comm.
          simpl.
          apply Lt.lt_n_S.
          apply H2. }
      apply H8.
  intros H1.
  intros H2.
