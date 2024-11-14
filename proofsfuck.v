
Lemma my_eq_sym: forall a b : Set, a = b -> b = a.
Proof.
  intros a b.
  intros H.
  rewrite -> H || rewrite <- H.
  reflexivity.
Qed.

Ltac inv H := inversion H; clear H; try subst.

Inductive expr : Set :=
  | EInt : nat -> expr
  | EAdd : expr -> expr -> expr
  | EMul : expr -> expr -> expr.

Inductive eval : expr -> nat -> Prop := 
  | eval_int : forall n, eval (EInt n) n
  | eval_add : forall e e' n m,
      eval e n -> 
      eval e' m -> 
        eval (EAdd e e') (n + m)
  | eval_mul : forall e e' n m,
      eval e n -> 
      eval e' m -> 
        eval (EMul e e') (n * m).

Fixpoint sem (e : expr) : nat := 
  match e with
  | EInt n => n
  | EAdd n m => sem n + sem m
  | EMul n m => sem n * sem m
  end.

Notation "[[ x ]]" := (sem x).

Compute [[ EInt 2 ]].

Theorem sem_correct:
  forall e n,
    eval e n <-> [[ e ]] = n.
Proof.
  intros e n.
  split.
  - intros Heval.
    induction Heval.
    + reflexivity.
    + simpl. rewrite IHHeval1. rewrite IHHeval2. reflexivity.
    + simpl. rewrite IHHeval1. rewrite IHHeval2. reflexivity.
  - intros Hsem.

    generalize dependent n.
    induction e.
    + intros n' Hsem. simpl in Hsem. rewrite Hsem. apply eval_int.
    + intros n' Hsem. simpl in Hsem. rewrite <- Hsem. apply eval_add. 
      * apply IHe1. reflexivity.
      * apply IHe2. reflexivity.
    + intros n' Hsem. simpl in Hsem. rewrite <- Hsem. apply eval_mul. 
      * apply IHe1. reflexivity.
      * apply IHe2. reflexivity.
Qed.

Theorem eval_deterministic: 
  forall e a b,
    eval e a -> 
    eval e b -> 
      a = b.
Proof.
  intros e a b.
  intros Heval1 Heval2.
  apply sem_correct in Heval1.
  apply sem_correct in Heval2.
  rewrite Heval1 in Heval2.
  assumption.
Qed. 

Theorem sem_eval:
  forall e, eval e [[ e ]].
Proof.
  intros e.
  pose proof (sem_correct e [[ e ]]) as H.
  apply H.
  reflexivity.
Qed.




