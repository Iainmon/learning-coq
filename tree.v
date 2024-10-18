


Inductive tree (A : Type) : Type :=
  | empty : tree A
  | node : A -> tree A -> tree A -> tree A.

Arguments empty {A}%type_scope.
Arguments node {A}%type_scope _ _ _.

Fixpoint height {A : Type} (tr : tree A) : nat :=
  match tr with
  | empty => 0
  | node _ t1 t2 => 1 + height t1 + height t2
  end.






(*
Inductive tree (A : Type) : Type :=
  | leaf : A -> tree A
  | node : A -> tree A -> tree A -> tree A.


(* Arguments tree {A}%type_scope. *)
Arguments leaf {A}%type_scope _.
Arguments node {A}%type_scope _ _ _.

Fixpoint height {A : Type} (t : tree A) : nat :=
  match t with
  | leaf _ => 0
  | node _ t1 t2 => 1 + max (height t1) (height t2)
  end.

*)