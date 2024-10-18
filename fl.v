

Require Import ZArith.
Open Scope Z_scope.

Require Import Strings.String.
Open Scope string_scope.

Definition name := string.

Inductive expr : Set :=
  | EVar : name -> expr
  | EInt : Z -> expr
  | EAdd : expr -> expr -> expr
  | ESub : expr -> expr -> expr
  | EMul : expr -> expr -> expr
  | EDiv : expr -> expr -> expr
  | ELt : expr -> expr -> expr
  | EEq : expr -> expr -> expr.

(* Notation "'evar' x" := (EVar x) (at level 85). *)
(* Notation "'eval' x" := (EInt x) (at level 85). *)
Notation "a 'e+' b" := (EAdd a b) (at level 80).
Notation "a 'e-' b" := (ESub a b) (at level 80).
Notation "a 'e*' b" := (EMul a b) (at level 70).
Notation "a 'e/' b" := (EDiv a b) (at level 70).
Notation "a 'e<' b" := (ELt a b) (at level 70).
Notation "a 'e=' b" := (EEq a b) (at level 70).

Inductive stmt : Set :=
  | SAssign : name -> expr -> stmt
  | SSeq : stmt -> stmt -> stmt
  | SIf : expr -> stmt -> stmt -> stmt
  | SRep : expr -> stmt -> stmt
  | SSkip : stmt.

Definition state := name -> option Z.


Definition patch (s : state) (x : name) (z : option Z) : state :=
  fun y => if string_dec x y then z else s y.

Definition update (s : state) (x : name) (z : Z) : state :=
  patch s x (Some z).

Definition empty : state := fun (x : name) => None.


Compute (update empty "x" 3 "x").

(* Search (?a -> option ?a).
Search ((?a -> ?b) -> option ?a -> option ?b).
Search (option ?A -> (?A -> option ?B) -> option ?B). *)

Definition option_bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Definition maybe {A B : Type} (b : B) (f : A -> B) (a : option A) : B :=
  match a with
    | None => b
    | Some x => f x
  end.

Definition option_map_2 {A B C : Type} (f : A -> B -> C) (a : option A) (b : option B) : option C :=
  option_bind a (fun x => option_map (f x) b).

Definition eval_bin_op (f : Z -> Z -> Z) (v1 v2 : option Z) : option Z :=
  option_map_2 f v1 v2.

Fixpoint eval_expr (e : expr) (s : state) : option Z :=
  match e with
  | EVar x => s x
  | EInt z => Some z
  | EAdd e1 e2 => eval_bin_op Z.add (eval_expr e1 s) (eval_expr e2 s)
  | ESub e1 e2 => eval_bin_op Z.sub (eval_expr e1 s) (eval_expr e2 s)
  | EMul e1 e2 => eval_bin_op Z.mul (eval_expr e1 s) (eval_expr e2 s)
  | EDiv e1 e2 => eval_bin_op Z.div (eval_expr e1 s) (eval_expr e2 s)
  | ELt e1 e2 => eval_bin_op (fun x y => if Z.ltb x y then 1 else 0) (eval_expr e1 s) (eval_expr e2 s)
  | EEq e1 e2 => eval_bin_op (fun x y => if Z.eqb x y then 1 else 0) (eval_expr e1 s) (eval_expr e2 s)
  end.

Notation "[[ e ]]" := (eval_expr e) (at level 90).
Notation "[[ e ]] 'in' s" := (eval_expr e s) (at level 90).

Require Import List.
(* Import ListNotations. *)

Fixpoint list_state (l : list (name * Z)) : state :=
  match l with
  | nil => empty
  | (x, z) :: xs => update (list_state xs) x z
  end.

Inductive exec_stmt : state -> stmt -> state -> Prop :=
  | evec_assign : forall st x e v,
    ([[e]] in st) = Some v ->
      exec_stmt st (SAssign x e) (update st x v)
  | exec_seq : forall st st' st'' s1 s2,
    exec_stmt st s1 st' ->
    exec_stmt st' s2 st'' ->
      exec_stmt st (SSeq s1 s2) st''
  | exec_if_true : forall st st' s1 s2 e v,
    ([[e]] in st) = Some v ->
    v > 0 ->
    exec_stmt st s1 st' ->
      exec_stmt st (SIf e s1 s2) st'
  | exec_if_false : forall st st' s1 s2 e v,
    ([[e]] in st) = Some v ->
    v < 1 ->
    exec_stmt st s2 st' ->
      exec_stmt st (SIf e s1 s2) st'
  | exec_rep_zero : forall st e s v,
    ([[e]] in st) = Some v ->
    v < 1 ->
      exec_stmt st (SRep e s) st
  | exec_rep : forall st st' st'' e s v,
    ([[e]] in st) = Some v ->
    v > 0 ->
    exec_stmt st s st' ->
    exec_stmt st' (SRep (e e- (EInt 1)) s) st'' ->
      exec_stmt st (SRep e s) st''
  | exec_skip : forall st,
    exec_stmt st SSkip st.

Lemma no_name: forall st st' s1 s2,
  exec_stmt st s1 st' ->
  
  exec_stmt st (SSeq s1 s2) st'.


(* Search "_ ?= _".

Search Z.eqb.

About Zpos.
Print positive.

Search (Z -> nat).
Search (nat -> Z).

Search (?a = ?b) (?b = ?a). *)


Compute eq_sym.


Fixpoint eval_stmt (s : stmt) (st : state) : state :=
  match s with
  | SAssign x e => patch st x (eval_expr e st)
  | SSeq s1 s2 => eval_stmt s2 (eval_stmt s1 st)
  | SIf e s1 s2 => 
    maybe empty (fun x => if Z.eqb x 1 then eval_stmt s1 st else eval_stmt s2 st) (eval_expr e st)
  | SRep e s1 => 
    maybe empty (fun x => 
      match (Z.to_nat x) with
      | (S x') => eval_stmt (SRep (EInt (Z.of_nat x')) s1) (eval_stmt s1 st)
      | _ => st
      end) (eval_expr e st)
  | SSkip => st
  end.



