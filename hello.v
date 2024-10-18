




Compute 1 + 1.



Theorem hello : 1 + 1 = 2.
Proof. reflexivity. Qed.


Require Import List.
Import ListNotations.
Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

Print hello.

