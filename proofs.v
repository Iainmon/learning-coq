
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

Inductive sem_eq: expr -> expr -> Prop :=
  | sem_eval_eq : forall e1 e2,
    [[ e1 ]] = [[ e2 ]] -> sem_eq e1 e2.

Lemma sem_eq_corollary_1:
  forall e1 e2,
    sem_eq e1 e2 -> 
    forall n, 
      eval e1 n <-> 
        eval e2 n.
Proof.
  intros e1 e2.
  intros H1.
  inversion H1.
  subst.
  pose proof H as H3.
  remember [[ e1 ]] as m in H3.
  apply eq_sym in H3.
  apply eq_sym in Heqm.
  intros n.
  split.
  -
    intros H4.
    apply sem_correct in H4.
    rewrite Heqm in H4.
    apply sem_correct.
    rewrite H3.
    assumption.
  -
    intros H4.
    apply sem_correct in Heqm.
    rewrite <- H3 in Heqm.
    apply sem_correct in H4.
    rewrite <- H4.
    assumption.
Qed.


Lemma sem_eq_corollary_2:
  forall e1 e2,
    (forall n, eval e1 n <-> eval e2 n) ->
      [[ e1 ]] = [[ e2 ]].
Proof.
  intros e1 e2.
  intros H1.
  pose proof (sem_correct e1 [[ e2 ]]) as H2.
  pose proof (sem_correct e2 [[ e1 ]]) as H3.
  pose proof (H1 [[ e1 ]]) as H4.
  pose proof (sem_eval e1) as H5.
  apply H4 in H5.
  apply H3 in H5.
  apply eq_sym.
  assumption.
Qed.

Lemma sem_eq_corollary_3:
  forall e1 e2,
    sem_eq e1 e2 <-> [[ e1 ]] = [[ e2 ]].
Proof.
  intros e1 e2.
  split.
  - intros H1.
    inversion H1.
    assumption.
  - intros H1.
    apply sem_eval_eq.
    assumption.
Qed.

Lemma sem_eq_corollary_4:
  forall e1 e2,
    (forall n, eval e1 n <-> eval e2 n) <-> 
      [[ e1 ]] = [[ e2 ]].
Proof.
  intros e1 e2.
  split.
  - intros H1.
    apply sem_eq_corollary_2.
    assumption.
  - intros H1.
    apply sem_eq_corollary_1.
    apply sem_eval_eq.
    assumption.
Qed.


Theorem semantic_equivalence:
  forall e1 e2,
    (sem_eq e1 e2 <-> [[ e1 ]] = [[ e2 ]]) /\
    ([[ e1 ]] = [[ e2 ]] <-> forall n, eval e1 n <-> eval e2 n) /\
    ((forall n, eval e1 n <-> eval e2 n) <-> sem_eq e1 e2).
Proof.
  intros e1 e2.
  split.
  - apply sem_eq_corollary_3.
  - split.
   + split.
    * apply sem_eq_corollary_4.
    * apply sem_eq_corollary_2.
   + split.
    * intros H1.
      apply sem_eval_eq.
      apply sem_eq_corollary_2.
      assumption.
    * apply sem_eq_corollary_1.
Qed.

(* Fixpoint all_equivalent: list Prop -> Prop := Admitted. *)

Print eq.

Inductive rel_correct {A B : Type} : (A -> B -> Prop) -> (A -> B) -> Prop :=
  | rel_correct_extensibility : 
    forall (R : A -> B -> Prop) (f : A -> B),
      (forall a b, R a b <-> f a = b) -> 
        rel_correct R f.
(* Arguments rel_correct {A B} R f. *)
(* Arguments rel_correct {A B}%type_scope. *)

Print Implicit rel_correct.
Print Implicit eq.

Lemma functional_relation: 
  forall {A B : Type} 
         (R : A -> B -> Prop) 
         (f : A -> B),
    rel_correct R f -> forall a, R a (f a).
Proof.
  intros A B.
  intros R f.
  intros H.
  inversion H.
  subst.
  intros a.
  apply H0.
  reflexivity.
Qed.

Lemma deterministic_relation: 
  forall {A B : Type} 
         (R : A -> B -> Prop) 
         (f : A -> B),
    rel_correct R f -> 
      forall a b c, R a b -> R a c -> b = c.
Proof.
  Admitted.


Theorem no_name: 
  forall (A B : Type)
         (R : A -> B -> Prop)
         (f : A -> B),
    (forall a b, R a b <-> f a = b) -> forall a, R a (f a).
Proof.
  intros A B R f.
  intros H.
  intros a.
  apply H.
  reflexivity.
Qed.




