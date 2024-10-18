

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.

Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition name : Type := string.

Definition atom : Type := name.

Inductive term : Type :=
  | term_structure : name -> list term -> term
  | term_var       : name -> term
  | term_int       : nat -> term.

Inductive predicate : Type :=
  | predicate : name -> list term -> predicate.
  

Inductive rule : Type :=
  | rule : term -> term -> rule.
