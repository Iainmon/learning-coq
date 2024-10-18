Require Import Unicode.Utf8.


Theorem my_theorem:
  forall (A : Type) (x y : A),
    x = y <-> (forall P : A -> Prop, P x <-> P y).
Proof.
  intros A x y.
  split.
  - intros H1. (* Show Proof. *)
    rewrite H1.
    intros P.
    split; intros; assumption.
  - intros H2.
    apply H2.
    reflexivity.
Qed.


About eqb.


Ltac msimpl := progress simpl.

Theorem plus_1_neq_0:
  forall (n : nat),
    (n + 1 <> 0).
Proof.
  intros n.
  destruct n as [ | n'] eqn:E.
  - msimpl. discriminate.
  - msimpl. discriminate.
Qed.


Require Import Coq.Arith.Plus.
Require Import Le.
Require Import Lt.

Open Scope nat_scope.

Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m.
  elim n; simpl in |- *.
  auto with arith.
  Show Proof.
  intros y H; elim (plus_n_Sm m y); auto with arith.
Qed.

Check nat_ind.
Locate nat_ind.

Lemma plus_n_0 : forall n, n = n + 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.


Theorem plus_monotonic:
  forall (n m : nat),
    n <= n + m.
Proof.
  intros n m.
  induction m.
  - rewrite <- plus_n_0.
    apply le_n.
  - rewrite <- plus_Snm_nSm.
    simpl.
    apply le_S.
    assumption.
Qed.  

Check plus_Snm_nSm.

Print nat.

Fixpoint max n m {struct n} : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.



Inductive tree (A : Type) : Type :=
  | empty : tree A
  | node : A -> tree A -> tree A -> tree A.

Arguments empty {A}%type_scope.
Arguments node {A}%type_scope _ _ _.

Fixpoint height {A : Type} (tr : tree A) : nat :=
  match tr with
  | empty => 0
  | node _ t1 t2 => 1 + max (height t1) (height t2)
  end.

Print nat.


Lemma max_comm :
  forall n m, max n m = max m n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma max_zero_a :
  forall a b, 
    max a b = 0 -> a = 0. 
Proof. 
  intros a b. 
  intros H1.
  induction a.
  - reflexivity.
  - destruct b.
    + discriminate.
    + discriminate.
Qed.

Lemma max_zero :
  forall a b, 
    max a b = 0 -> a = 0 /\ b = 0. 
Proof. 
  intros a b. 
  intros H1.
  split.
  - apply (max_zero_a a b).
    assumption.
  - rewrite max_comm in H1.
    apply (max_zero_a b a).
    assumption.
Qed.


Lemma my_max_l :
  forall n m, 
    m <= n -> max n m = n.
Proof.
  induction n; induction m; simpl in |- *; auto with arith.
Qed.

Lemma max_monotonic: 
  forall a b x y, 
    a <= x -> 
    b <= y -> 
      max a b <= max x y.
Proof.
  induction a; induction b; simpl in |- *; auto with arith.

  (* intros a b x y.
  intros H1 H2. *)

  


Lemma height_swap_eq :
  forall A (t t' : tree A) (a : A),
    height (node a t t') = height (node a t' t).
Proof.
  intros A t t' a.
  simpl.
  apply f_equal.
  apply max_comm.
Qed.


Fixpoint sum_tree (t : tree nat) : nat := 
  match t with
  | empty => 0
  | node n t1 t2 => n + sum_tree t1 + sum_tree t2
  end.

Lemma sum_tree_node :
  forall t1 t2 n,
    n = sum_tree t1 + sum_tree t2 -> 
      forall m,
        n + m = sum_tree (node m t1 t2).
Proof.
  intros t1 t2 n.
  intros H.
  intros m.
  rewrite H.
  simpl.
  rewrite plus_comm.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.



Fixpoint size {A : Type} (t : tree A) : nat :=
  match t with
  | empty => 0
  | node _ t1 t2 => 1 + (size t1) + (size t2)
  end.

Lemma height_lte_size:
  forall A (t : tree A),
    height t <= size t.
Proof.
  intros A.
  intros t.
  induction t.
  - simpl. apply le_n.
  - simpl.
    apply le_n_S.
    Check Nat.le_trans.
    apply Nat.le_trans with (m := max (size t1) (size t2)).
    + Search "a <= x -> b <= y -> max a b <= max x y"
    
    apply Nat.le_max_l.
    Check le_S_n.

    apply le_n_S.
    apply le_S_n.
    













(*

Inductive all_less_than (x : nat) : tree nat -> Prop :=
  | all_less_than_leaf : 
    forall n,
      n < x ->
      all_less_than x (leaf n)
  | all_less_than_node : 
    forall n l r,
      n < x ->
      all_less_than x l ->
      all_less_than x r ->
        all_less_than x (node n l r).

Inductive all_greater_than (x : nat) : tree nat -> Prop :=
  | all_greater_than_leaf : 
    forall n,
      x < n ->
        all_greater_than x (leaf n)
  | all_greater_than_node : 
    forall n l r,
      x < n ->
      all_greater_than x l ->
      all_greater_than x r ->
        all_greater_than x (node n l r).

Inductive binary_nat_tree : tree nat -> Prop :=
  | binary_leaf : 
    forall n, binary_nat_tree (leaf n)
  | binary_node : 
    forall n l r,
      binary_nat_tree l ->
      binary_nat_tree r ->
      all_less_than n l ->
      all_greater_than n r ->
        binary_nat_tree (node n l r).

Print Nat.eqb.

Fixpoint bst_insert (n : nat) (t : tree nat) : tree nat :=
  match t with
  | leaf m => 
    match n =? m, n <? m with
    | true, _ => t
    | _, true => node m (leaf n) (leaf m)
    | _, _    => node m (leaf m) (leaf n)
    end
  | node m t1 t2 =>
    match n =? m, n <? m with
    | true, _ => node m t1 t2
    | _, true => node m (bst_insert n t1) t2
    | _, _    => node m t1 (bst_insert n t2)
    end
  end.


Ltac mrewrite H :=
  rewrite H || rewrite <- H.
  (* repeat match goal with
  | [ |- context[?n =? ?m] ] => destruct (n =? m) eqn:?
  | [ |- context[?n <? ?m] ] => destruct (n <? m) eqn:?
  end. *)


Fixpoint tree_max (t : tree nat) : nat :=
  match t with
  | leaf n => n
  | node n t1 t2 => 
    let n1 := tree_max t1 in
    let n2 := tree_max t2 in
      max n (max n1 n2)
  end.

Lemma tree_sum_bounded : 
  forall t m h, 
    m = tree_max t -> 
    h = height t -> 
    sum_tree t <= m * (2 ^ h).
Proof.
  intros t m h.
  intros H1.
  intros H2.
  Print "<=".
  induction t.
  - simpl in *.
    rewrite H2.
    simpl.
    Search (_ * _ = _ * _).
    replace (m * 1) with m.
    2: { rewrite Nat.mul_comm.  }
    rewrite H1.
    apply le_n.
  - induction m.
    + simpl in H1. (* use helper lemma here *)
      assert (a = 0 /\ max (tree_max t1) (tree_max t2) = 0) as H3.
      { apply eq_sym in H1. apply (max_zero a (max (tree_max t1) (tree_max t2))).
        assumption. }
      destruct H3 as [H3 H4].
      simpl.
      rewrite H3.
      simpl.
      Check Nat.le_0_r.
      apply Nat.le_0_r.
      apply max_zero in H4 as H5.
      destruct H5 as [H5 H6].

      generalize dependent h.


      congruence.



      destruct H1 as [H1 H3].
      rewrite H1.
      simpl.
      apply le_0_n.
Admitted.
*)


Lemma tree_for_all_nats :
  forall n : nat, 
    exists t : tree nat,
      n = sum_tree t.
Proof.
  intros n.
  exists (leaf n).
  simpl.
  reflexivity.
Qed.



  simpl in *.
    Print "^".
    rewrite H2.
    destruct m.
    + 

    rewrite H1.
    simpl.




Lemma 





    Print le.
  Locate "_ <= _". 



  Locate "_ <> _".

  simpl.
  unfold "<>".