Require Import Unicode.Utf8.

Require Import Psatz.
Require Import Coq.Arith.Plus.


Inductive tree : Type :=
  | empty : tree
  | node : tree -> tree -> tree.

Fixpoint height (t : tree) : nat :=
  match t with
  | empty => 0
  | node l r => S (max (height l) (height r))
  end.

Fixpoint size (t : tree) : nat :=
  match t with
  | empty => 0
  | node l r => S (size l + size r)
  end.

Fixpoint exp2 (arg : nat) :=
  match arg with
  | O => 1
  | S n => exp2 n + exp2 n
  end.

Lemma exp2_eq_ex_2n : forall (n : nat), exp2 n = 2 ^ n.
Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. lia.
Qed.   

Lemma exp2_geq_1 : forall (n : nat), 1 <= exp2 n.
Proof.
    induction n.
    - simpl. lia.
    - simpl. lia.
Qed.   

Lemma exp2_preserves_leq : forall (n m : nat), n <= m -> exp2 n <= exp2 m.
Proof.
  intros n. induction n; intros m Hnm.
  - simpl. apply exp2_geq_1.
  - simpl. destruct m.
    + inversion Hnm.
    + simpl. specialize (IHn m (le_S_n n m Hnm)). lia.
Qed.

Theorem one_number_less : forall (n m : nat), n <= m \/ m <= n.
Proof.
  intros n. induction n; intros m; destruct m; auto.
  - left. apply le_0_n.
  - right. apply le_0_n.
  - destruct (IHn m).
    + left. apply le_n_S; auto.
    + right. apply le_n_S; auto.
Qed.

Theorem height_power_of_two : forall (t : tree), S (size t) <= exp2 (S (height t)).
Proof.
  intros t. induction t.
  - simpl; auto.
  - remember (height (node t1 t2)) as h.
    simpl. rewrite Heqh. simpl.

    remember (height t1) as h1.
    remember (height t2) as h2.
    remember (size t1) as s1.
    remember (size t2) as s2.


    simpl in IHt1. simpl in IHt2.
    destruct (one_number_less h1 h2).
    + rewrite (max_r h1 h2 H).
      specialize (exp2_preserves_leq h1 h2 H) as Hexp. lia.
    + rewrite (max_l h1 h2 H).
      specialize (exp2_preserves_leq h2 h1 H) as Hexp. lia.
Qed.