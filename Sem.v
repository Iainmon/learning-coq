Require Import Coq.Strings.String.
Open Scope string_scope.

Variable n n1 n2 n3 : nat.

Definition env := string -> option nat.
Variable E E1 E2 E3 : env.

Inductive expr : Set :=
  | EVar : string -> expr
  | EInt : nat -> expr
  | EAdd : expr -> expr -> expr
  | EMul : expr -> expr -> expr.

Inductive eval : env -> expr -> nat -> Prop :=
  | eval_var : forall E S n, E S = Some n -> eval E (EVar S) n
  | eval_int : forall E n, eval E (EInt n) n
  | eval_add : forall E e1 e2 n1 n2,
      eval E e1 n1 ->
      eval E e2 n2 ->
        eval E (EAdd e1 e2) (n1 + n2)
  | eval_mul : forall E e1 e2 n1 n2,
      eval E e1 n1 ->
      eval E e2 n2 ->
        eval E (EMul e1 e2) (n1 * n2).

Fixpoint sem (e : expr) (E : env) : option nat :=
  match e with
  | EVar s => E s
  | EInt n => Some n
  | EAdd e1 e2 =>
      match sem e1 E, sem e2 E with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | EMul e1 e2 =>
      match sem e1 E, sem e2 E with
      | Some n1, Some n2 => Some (n1 * n2)
      | _, _ => None
      end
  end.

Notation "[[ x ]]" := (sem x).

Theorem expr_eval_sem : forall E e n, eval E e n -> [[ e ]] E = Some n.
Proof.
  intros E e; induction e; intros n Heval.
  all: inversion Heval.
  all: subst.
  all: simpl.
  all: auto.
  all: specialize (IHe1 n4 H2).
  all: specialize (IHe2 n5 H4).
  all: rewrite IHe1.
  all: rewrite IHe2.
  all: try reflexivity.
Qed.




Theorem expr_sem_eval : 
  forall E e n, 
    [[ e ]] E = Some n -> eval E e n.
Proof.
  intros E e.
  induction e.
  all: intros n Heq.
  simpl in Heq.
  constructor. 
  assumption. 
  inversion Heq.
  constructor.
  all: simpl in Heq.
  all: destruct ([[e1]] E) as [n1|] eqn:H1
  ; destruct ([[e2]] E) as [n2|] eqn:H2
  . specialize (IHe1 n2 H1).
  
  assert ([[e1]] E = Some n1).
  { 

    }
  destruct ([[e1]] E) as [n1|] eqn:H1.


  inversion Heq.




Theorem expr_sem_eval : 
  forall E e n, 
    [[ e ]] E = Some n -> eval E e n .
Proof.
  intros E e; induction e; intros n Heq; simpl.
  - 

Inductive stmt : Set :=
  | SSeq : stmt -> stmt -> stmt
  | SAssign : string -> expr -> stmt
  | SIf : expr -> stmt -> stmt -> stmt
  | SWhile : expr -> stmt -> stmt.


Inductive stmt_sem : env -> stmt -> env -> Prop :=
  | eval_seq : stmt_sem e1 s1 e2 ->
               stmt_sem e2 s2 e3 ->
               stmt_sem e1 (SSeq s1 s2) e3
  | eval_assign : 
