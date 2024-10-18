


Lemma no_name: forall (A : Type) (a b : A),
    (forall P : A -> Prop, P a <-> P b) <-> a = b.


(* daniels proof *)
Proof.
  intros A a b.
  split.
  - intros HP. 
    specialize (HP (eq a)).
    apply HP.
    reflexivity.
  - intros HP.
    intros P.
    split; intros H; try rewrite HP; try (rewrite HP in H); assumption.
Qed.

Lemma no_name_2: forall (A : Type) (a b : A),
    (forall P : A -> Prop, P a -> P b) -> a = b.
Proof.
  intros A a b.
  intros H.
  specialize (H (eq a)).
  apply H.
  reflexivity.
Qed.

(* my proof 
Proof.
    intros A a b.
    split.
    - intros H.
      pose proof (fun x : A => x = a) as H2.

      pose proof (H (fun x : A => x = a)) as H3.
      pose proof (eq_refl a) as H4.
      apply H3 in H4.
      apply eq_sym.
      assumption.
    - intros H.
      rewrite H.
      intros P.
      tauto. 

Qed.
*)




Require Import Nat.



Definition group (P : Prop) := P.

Lemma group_fold : forall (P: Prop), P -> group P.
Proof. Admitted.

(* Proof. auto. Qed. *)

About group_fold.

Ltac my_tactic := 
  match goal with
  | H : _ |- _ => constr:(H)
  end.

Lemma no_name_1: forall (A : Type) (a b : A),
  a = b -> b = a.
Proof.
  intros.
  exact (eq_sym H).
Qed.
Print no_name_1.

Ltac destruct_if :=
  match goal with
  | [ H : if ?cond then _ else _ |- _ ] => destruct cond
  end.

Search (nat -> bool).
About leb.

Compute (leb 0 1).

Print leb.

Ltac new_var :=
  let x := fresh "x" in
  pose proof (eq_refl 1) as x.

Ltac know a b new_hyp :=
  match goal with
  | [H : a = b |- _] => pose proof H as new_hyp
  | [H : b = a |- _] => pose proof (eq_sym H) as new_hyp
  end.

Tactic Notation "know" a "=" b "as" new_hyp :=
  know a b new_hyp.

Ltac trans new_hyp :=
  match goal with
  | [H1 : ?a = ?b, H2 : ?b = ?c |- _] => 
    pose proof (eq_trans H1 H2) as new_hyp
  | [H1 : ?b = ?a, H2 : ?b = ?c |- _] => 
    pose proof (eq_trans (eq_sym H1) H2) as new_hyp
  | [H1 : ?a = ?b, H2 : ?c = ?b |- _] => 
    pose proof (eq_trans H1 (eq_sym H2)) as new_hyp
  | [H1 : ?b = ?a, H2 : ?c = ?b |- _] => 
    pose proof (eq_trans (eq_sym H1) (eq_sym H2)) as new_hyp
  (* | [H1 : ?a = ?b, H2 : ?c = ?b |- _] => 
    let nh := fresh new_hyp in
      pose proof (eq_trans (eq_sym H1) H2) as nh *)
  | _ => idtac new_hyp
  (* | [H1 : ?a = ?b, H2 : ?c = ?b |- _]
  => 
    let nh1 := fresh new_hyp in
    let nh3 := fresh new_hyp in
    let nh2 := fresh new_hyp in
    (try (pose proof (eq_trans (eq_sym H1) H2) as nh1));
    (try (pose proof (eq_trans H1 (eq_sym H2)) as nh2));
    try (pose proof (eq_trans (eq_sym H1) (eq_sym H2)) as nh3)
  | [H1 : ?b = ?a, H2 : ?c = ?b |- _]
  => 
    let nh1 := fresh new_hyp in
    let nh3 := fresh new_hyp in
    let nh2 := fresh new_hyp in
    (try (pose proof (eq_trans (eq_sym H1) H2) as nh1));
    (try (pose proof (eq_trans H1 (eq_sym H2)) as nh2));
    try (pose proof (eq_trans (eq_sym H1) (eq_sym H2)) as nh3) *)
  (* | [H1 : ?a = ?b, H2 : ?c = ?b |- _] => pose proof (eq_trans H1 (eq_sym H2)) as new_hyp
  | [H1 : ?b = ?a, H2 : ?c = ?b |- _] => pose proof (eq_trans (eq_sym H1) (eq_sym H2)) as new_hyp *)
  end.

Lemma nn: forall a b c : nat, a = b -> c = b -> a = c.
Proof.
  intros a b c H0 H1.
  trans H3.
  assumption.
Qed.

  transitivity b.
  - assumption.
  - assumption.
Qed.

Lemma trivial_lemma: forall (a b : nat),
  (if eqb a b then a = b else a = a) -> a = a.
Proof.
  intros a b.
  intros H.
  new_var.
  destruct x.
  destruct x.
  destruct (a =? b).
  destruct_if.



Ltac my_tac ()

Lemma no_name_test_1:
  forall n : nat,
    n > 0 -> 
      1 + n = S n.
Proof.
  intros n.
  intros H.



Ltac find_group :=
  match goal with
  | H : group _ |- _ => constr:(H)
  end.

