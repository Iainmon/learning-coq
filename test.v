(* Define the vector type *)
Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall (n : nat), A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A n} _ _.

(* Define the zipWith function *)
Fixpoint zipWith {A B C : Type} {n : nat}
                 (f : A -> B -> C)
                 (v1 : vector A n)
                 (v2 : vector B n) : vector C n :=
  match n with
  | 0 => vnil  (* Base case: vectors of length 0 *)
  | S n' =>     (* Recursive case: vectors of length S n' *)
      match v1, v2 with
      | vcons a v1', vcons b v2' =>
          vcons (f a b) (zipWith f v1' v2')  (* Recursive call *)
      end
  end.