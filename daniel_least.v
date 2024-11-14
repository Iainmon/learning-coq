Require Import Unicode.Utf8.
Require Import Psatz.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat. (* needed? it seems no, with next line. *)
Import Nat.

Definition nat_set (f : nat -> Prop) := (forall n, f n \/ ~ f n).

Definition nonempty (f : nat -> Prop) := exists n, f n.

Lemma le_dec :
  forall n m, n <= m \/ m < n.
Proof. lia. Qed.

Lemma least_element_help :
  forall f,
     nat_set f ->
  forall k least,
    f least ->
    (forall k', k < k' -> k' < least -> ~ f k') -> (* no smaller element above k that is in f *)
    exists n, f n /\ forall m, f m -> n <= m.
Proof.
  intros f Hnsf k.
  induction k; intros least Hleast Hinv.
  - destruct (Hnsf 0).
    + (* Case 1: k is zero and it's in the set. It is trivially the least element. *)
      exists 0. split; auto. intros m Hfm. apply le_0_n.
    + (* Case 2: k is zero and it's not in the set. That means our 'least
         candidate' is the least element. *)
      exists least. split. auto.

      (* To prove that least is really least, need to show others are bigger. *)
      intros [|m'] Hfm.
      * exfalso. apply H. apply Hfm.  (* zero may or may not be >= than least, but it's not in the set. *)
        (* destruct (H Hfm). *)
      * (* Our nonzero 'other' is either bigger or less than the candidate.
           If it's bigger, we're done; if it's smaller, our invariant states
           it can't be in the set. *)
        destruct (le_dec least (S m')). assumption.
    
        specialize (Hinv (S m')).
        specialize (Hinv (le_n_S 0 m' (le_0_n m'))).
        exfalso. apply Hinv. assumption. assumption.
        (* this is the 'smaller' case, apply invariant. *)
        (* destruct (Hinv (S m') (le_n_S 0 m' (le_0_n m')) H0 Hfm). *)
  - destruct (Hnsf (S k)).
    + (* Case 3: k is nonzero, and in the set. It's now our new 'least candidate'.
         Apply the induction hypothesis with the new candidate. *)
      eapply IHk. apply H.
      intros k'. lia.
    + (* Case 4: k is nonzero, and not in the set. Then we can strengthen our
         invariant, and use the same 'least candidate'. *)
      eapply IHk. apply Hleast.

      (* This is all the invariant strengthening; re-proving the invariant
         with a wider bound. *)
      intros k' Hkk' Hk'least. destruct (le_dec k' (S k)).
      * (* If k' is equal to our new low bound, it's k, and we know k is not in the set. *)
        inversion H0; auto. subst. lia.
      * (* If k' is bigger than our new low bound, we can defer to the original
           invariant. *)
        apply Hinv; auto.
Qed.

Lemma least_element :
  forall f,
    nat_set f ->
    nonempty f ->
    exists n, f n /\ forall m, f m -> n <= m.
Proof.
  intros f Hnsf [n Hfn].
  assert (forall k', n < k' -> k' < n -> ~ f k') by lia.
  apply (least_element_help f Hnsf n n Hfn H).
Qed.


Definition eq_set (n m : nat) : Prop :=
    if (Nat.eqb n m) then True else False.
    
Lemma eq_set_dec : forall n, nat_set (eq_set n).
Proof.
  intros n m.
  unfold eq_set.
  destruct (Nat.eqb n m); auto.
Qed.

Lemma eq_set_non_empty : forall n, nonempty (eq_set n).
Proof.
  intros n.
  exists n.
  unfold eq_set.
  rewrite Nat.eqb_refl.
  auto.
Qed.


Definition eq_1000 := eq_set 1000. 

Definition eq_least_element_1000 := least_element eq_1000 (eq_set_dec 1000) (eq_set_non_empty 1000).

Compute eq_least_element_1000.

Definition my_property (n : nat) := least_element (eq_set n) (eq_set_dec n) (eq_set_non_empty n).

Compute (my_property 3).



