Require Import Coq.Init.Nat.

Inductive bit : Set := I | O.

Inductive bits : nat -> Set :=
  | bnil  : bits 0
  | bcons : forall (n : nat), bit -> bits n -> bits (S n).
Arguments bcons {n} _ _.

Require Import List.
Import ListNotations.

Fixpoint bits_list (l : list nat) : bits (length l) :=
  match l with
  | [] => bnil
  | 0 :: l' => bcons O (bits_list l')
  | _ :: l' => bcons I (bits_list l')
  end.

Fixpoint list_bits {n : nat} (bs : bits n) : list nat :=
  match bs with
  | bnil => []
  | bcons O bs' => 0 :: (list_bits bs')
  | bcons I bs' => 1 :: (list_bits bs')
  end.

Definition my_bs := bits_list [1; 1; 0; 1; 1].
Compute my_bs.

Definition bits_length {n : nat} (bs : bits n) := n.

Definition bits_head {n : nat} (bs : bits (S n)) : bit :=
  match bs with
  | bcons b _ => b
  end.

Definition bits_tail {n : nat} (bs : bits (S n)) : bits n :=
  match bs with
  | bcons _ bs' => bs'
  end.

Definition bits_uncons {n : nat} (bs : bits (S n)) : bit * bits n :=
  (bits_head bs, bits_tail bs).

Fixpoint bits_app {n m : nat} (b1 : bits n) (b2 : bits m) : bits (n + m) :=
  match b1 with
  | bnil => b2
  | bcons b b1' => bcons b (bits_app b1' b2)
  end.

Definition bit_bin_op : Type := bit -> bit -> bit.

Definition bits_uncons2 (n : nat) (bs cs : bits (S n)) : (bit * bits n) * (bit * bits n) :=
  match bs, cs with
  | bcons b bs', bcons c cs' => ((b, bs'), (c, cs'))
  end.

Fixpoint bits_zip_with {n : nat}
                       (f : bit -> bit -> bit)
                       (bs cs : bits n) : bits n :=
  match bs, cs with
  | bnil, bnil => bnil
  | bcons b bs', bcons c cs' => bcons (f b c) (bits_zip_with f bs' cs')
  end.
