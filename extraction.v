

Require Import Unicode.Utf8.
Require Import Coq.Arith.Arith.
Import Nat.


Definition add (n m : nat) : nat := n + m.

Fixpoint my_add (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (my_add n' m)
  end.

Fixpoint my_mult (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => add m (my_mult n' m)
  end.

Fixpoint my_fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => my_mult n (my_fact n')
  end.

Inductive tree (A : Type) : Type :=
  | empty : tree A
  | node : tree A -> A -> tree A -> tree A.

Fixpoint height {A : Type} (t : tree A) : nat :=
  match t with
  | empty _ => 0
  | node _ l _ r => S (max (height l) (height r))
  end.

  


Require Import Coq.Arith.PeanoNat.

(************)
(* helper'' *)
(************)
Fixpoint helper' (p m n : nat) : bool :=
  match m,n with
  | 0,_ => false
  | 1,_ => false
  | _,0 => false
  | _,1 => false
  | S m',S n' => (orb ((mult m n) =? p) (helper' p m' n))
  end.

(**********)
(* helper *)
(**********)
Fixpoint helper (p m : nat) : bool :=
  match m with
  | 0 => false
  | S m' => (orb ((mult m m) =? p) (orb (helper' p m' m) (helper p m')))
  end.

Require Extraction.
Extraction Language Haskell.
Require Import ExtrHaskellBasic.



Require Import ExtrHaskellNatNum.

Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "Prelude.succ"].
(* Extraction "hello.hs" my_add helper helper'. *)

Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "(1+)"] "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extraction "hello.hs" my_add helper helper'.

(* Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "Prelude.succ"] "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extraction "hello.hs" my_add helper helper'. *)

Load "/Users/iainmoncrief/Documents/Github/statistics/Custom_plugin".
