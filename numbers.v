

Require Import Unicode.Utf8.

Require Import Psatz.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat. (* needed? it seems no, with next line. *)
Import Nat.

Open Scope nat_scope.

Check add_0_r.


Axiom give_up : forall (P : Prop), P.

Ltac give_up := apply give_up.

Goal 
  forall a b c d, 
    a <= b ->
    c <= d ->
    a + c <= b + d.
Proof.
  intros a b c d.
  lia.
Qed.


Goal forall (n m : nat),
  {n = m} + {n <> m}.
Proof.
  induction n.
  + intros m. destruct m.
    - left. reflexivity.
    - right. discriminate.  
  + destruct m.
    - right. discriminate.
    - pose proof (IHn m) as H1.
      inversion H1 as [H_eq | H_neq].
      * left. rewrite H_eq. reflexivity.
      * right. auto.
Qed. 


Check Nat.divide.




(* Inductive com_div : nat -> nat -> nat -> Prop :=
  | com_div_both : forall (a b d : nat),  *)

Definition common_div (a b d : nat) := (d | a) /\ (d | b).

Inductive greatest_common_div : nat -> nat -> nat -> Prop :=
  | divs_all_div : 
    forall a b d, 
      common_div a b d ->
      (forall d', common_div a b d' -> (d' | d)) ->
        greatest_common_div a b d.



Inductive nat_set : (nat -> Prop) -> Prop :=
  | dec_nat_set : forall (f : nat -> Prop),
    (forall n, f n \/ ~ f n) -> nat_set f.


Definition nonempty (f : nat -> Prop) := exists n, f n.


Lemma no_name_lemma_1:
  forall f, 
    nat_set f -> 
    nonempty f ->
    forall n, f n ->
      forall m, 
      m <= n -> f m \/ ~ f m.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.
  intros n.
  intros Hn.
  intros m.
  intros Hmn.
  apply Hf_dec.
Qed.

Definition is_min (f : nat -> Prop) := 
  fun n => f n /\ (forall k, k < n -> ~ f k).


(* Lemma nat_has_least_element :
  forall  *)


Fixpoint pred_elem f (n : nat) : Prop :=
  match n with
  | 0 => False
  | S n' => f n' \/ pred_elem f n'
  end.

Fixpoint no_pred_elem f (n : nat) : Prop :=
  match n with
  | 0 => ~ f n
  | S n' => (~ f n) /\ no_pred_elem f n'
  end.

Lemma pred_elem_exists :
  forall f, 
  nat_set f ->
  forall n, pred_elem f n <-> exists m, f m /\ m < n.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  induction n; split.
  - simpl. contradiction.
  - intros H2. 
    destruct H2 as [m [H2 H3]].
    apply Nat.nlt_0_r in H3.
    assumption.
  - intros H1.
    simpl in H1.
    destruct H1 as [H1 | H2].
    + exists n. auto. 
    + apply IHn in H2.
      destruct H2 as [m [H1 H2]].
      exists m.
      auto.
  - intros H1.
    destruct H1 as [m [H1 H2]].
    simpl.
    pose proof (Nat.eq_dec n m) as H3.
    destruct H3 as [Heq | Hneq].
    + left. rewrite Heq. assumption.
    + right. assert (m < n). { lia. }
      apply IHn.
      exists m. auto.
Qed.


Lemma pred_elem_dec : 
  forall f,
    nat_set f ->
    forall n, 
      pred_elem f n \/ ~ pred_elem f n.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  induction n.
  - right. simpl. auto.
  - simpl. destruct IHn as [H1 | H2].
    + left. auto.
    + destruct (Hf_dec n) as [H3 | H4].
      * left. auto.
      * right. 
        intros H. destruct H as [H5 | H6].
        -- apply H4. assumption.
        -- apply H2. assumption.
Qed.


Lemma least_element_helper : 
  forall f, 
    nat_set f -> 
    nonempty f ->
    forall k, (forall j, j < k -> ~ f j) \/ (exists j, j < k /\ f j).
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.

  induction k.
  - left. intros j Hj. simpl in Hj. lia.
  - 
    destruct IHk as [H1 | H2].
    + left. intros j. intros H2.  assumption.  
    destruct Hf_nem as [n Hn].
    exists n.
    split.
    + auto. 

Lemma least_element : 
  forall f, 
    nat_set f -> 
    nonempty f ->
    exists n, f n /\ forall m, f m -> n <= m.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.

  pose proof (no_name_lemma_1 f (dec_nat_set f Hf_dec) Hf_nem) as H2.






Lemma no_name_lemma_3 : 
  forall f, 
    nat_set f ->
    nonempty f ->
    exists n, ~ pred_elem f n /\ pred_elem f (S n).
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.

  pose proof (pred_elem_exists f (dec_nat_set f Hf_dec)) as H1.

  destruct Hf_nem as [k Hk].

  induction k.
  - exists 0. simpl. split.
    + auto.
    + left. assumption.
  - pose proof (Hf_dec k) as H2.
    pose proof (pred_elem_dec f (dec_nat_set f Hf_dec)) as H3.
    (***)
    destruct H2 as [Hfk | Hnfk].
    + apply IHk in Hfk. assumption.
    + (*pose proof (H3 k) as H4.
      pose proof (H3 (S k)) as H5.
      pose proof (H3 (S (S k))) as H6.*)

      (* pose proof (H1 k) as H6. *)
      simpl.
      assert ((exists n, ~ pred_elem f n /\ f n) -> (exists n, ~ pred_elem f n /\ pred_elem f (S n))).
      { simpl. intros H. destruct H as [x [Hx1 Hx2]]. exists x. split; try assumption. left. assumption. }
      apply H. (*clear H.*)
      pose proof (H3 (S k)) as H4.
      destruct H4 as [H4 | H4].
      * apply H1 in H4 as H5. 
        destruct H5 as [m [H5 H6]].
        pose proof (H3 m) as H7.
         admit.
      *   

      simpl in H4. simpl in H5. simpl in H6.
      destruct H5 as [H5 | H5].
      * exists (S k).
      * 
      split with k.
      exists (S k). split.
      * unfold not. intros H. 
           
      simpl in H5.
      (* pose proof (H3 (S (S k))) as H6. simpl in H6. *)

      pose proof (H1 (S (S k))) as H6.
      destruct H5 as [H5 | H5].
      *  
    
    
    destruct H3 as [H4 | H5].
      * exists k. simpl. split.
        -- auto.
        -- left. assumption.
      * exists (S k). simpl. split.
        -- auto.
        -- left. assumption. 
    
    admit. (*exists (S (S k)). simpl. split.
      * auto.
      * left. assumption.
     exists . simpl. split.
      * auto.
      * left. assumption.*)
  
Admitted.




Lemma no_name_lemma_2 : 
  forall f, 
    nat_set f -> 
    nonempty f ->
    forall n, 
      f n -> 
      pred_elem f n <-> exists m, m < n /\ f m.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.
  induction n; intros H1; split.
  - simpl. contradiction.
  - intros H2. 
    destruct H2 as [m [H2 H3]].
    apply Nat.nlt_0_r in H2.
    assumption.
  - generalize dependent n.
    intros H2.
    destruct H2 as [H2 | H2].
    Admitted.





Lemma least_element : 
  forall f, 
    nat_set f -> 
    nonempty f ->
    exists n, f n /\ forall m, f m -> n <= m.
Proof.
  intros f.
  intros Hf_ns.
  destruct Hf_ns as [f Hf_dec].
  intros Hf_nem.
  unfold nonempty in Hf_nem.

  pose proof (no_name_lemma_1 f (dec_nat_set f Hf_dec) Hf_nem) as H2.









(* Definition nat_set := nat -> Prop. *)

(* Definition dec_set ()  *)





split.



  induction a as [| a IH].
  - intros H1 H2.
    rewrite add_0_l.
    rewrite Nat.add_comm.
    Search (?a <= ?b -> ?a <= ?b + ?c).
    apply Nat.le_trans with (m := d).
    + assumption.
    + apply Nat.le_add_r.
  - intros H1 H2.
    simpl. (**)
    Search (S ?a <= ?b -> ?a <= ?b).
    apply Le.le_Sn_le_stt in H1.
    pose proof (IH H1 H2) as H3.
    Search (S ?a <= ?b). 

    destruct b; simpl in *.
    + inversion H1. 
    
    (**)

    rewrite Nat.add_succ_r.
    rewrite Nat.add_comm.
    rewrite Nat.add_comm with (n := d).
    lia. 

Qed.







