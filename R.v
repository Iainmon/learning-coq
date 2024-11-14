
Require Import Coq.Init.Nat.


Inductive bit : Set := I | O.

Inductive bits : nat -> Set :=
  | bnil  : bits 0
  | bcons : forall (n : nat), bit -> bits n -> bits (S n).
Arguments bcons [n] _ _.

Require Import List.
Import ListNotations.

Fixpoint from_list (l : list bit) : bits (length l) :=
  match l with
  | [] => bnil
  | b :: l' => bcons b (from_list l')
  end.

Fixpoint to_list {n : nat} (bs : bits n) : list bit :=
  match bs with
  | bnil => []
  | bcons b bs' => b :: (to_list bs')
  end.

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

Definition bits_uncons {n : nat} (bs : bits (S n)) : bit * bits n := (bits_head bs, bits_tail bs).

Fixpoint bits_app {n m : nat} (b1 : bits n) (b2 : bits m) : bits (n + m) :=
  match b1 (*in (bits n) return (bits (n + m))*) with
  | bnil => b2
  | bcons b b1' => bcons b (bits_app b1' b2)
  end.



Definition bit_bin_op : Type := bit -> bit -> bit.

Definition bits_uncons2 {n : nat} (bs cs : bits (S n)) : (bit * bits n) * (bit * bits n) :=
  match bs,cs with
  | bcons b bs',bcons c cs' => ((b,bs'),(c,cs'))
  end.

Check bits_uncons2.

Fixpoint bits_map {n : nat} (f : bit -> bit) (bs : bits n) : bits n :=
  match bs with
  | bnil => bnil
  | bcons b bs' => bcons (f b) (bits_map f bs')
  end.


Fixpoint zip_with {A B C : Type} (f : A -> B -> C)
  (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  end.


Fixpoint zipWith {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n.
  induction n.
  - 
  Show Proof. exact bnil.
  - inversion v1. inversion v2.
    rewrite <- H in * |- .
    rewrite H in * |- .
    apply bcons.
    exact (f H0 H3).
    exact (IHn H1 H4).
Defined.
Print zipWith.

(* read_me start *)


Print bits_head.
Print IDProp.
Check IDProp.
Check bits_head.


Definition head2 {n : nat} (bs cs : bits (S n)) : bit * bit :=
  match bs in (bits n'), cs in (bits n') with
  | bcons b _, bcons c _ => (b,c)
  end.
Print head2.

Definition head2' {n : nat} (bs cs : bits (S n)) : bit * bit :=
  match bs in (bits n) return match n with
                              | 0   => IDProp
                              | S _ => bit * bit
                              end
  with
  | bnil => idProp
  | @bcons n' b _ => 
    match cs in (bits n) return match n with
                                | 0   => IDProp
                                | S _ => bit * bit
                                end
    with
    | bnil => idProp
    | @bcons _ c _ => (b,c)
    end
  end.
Print head2'.

Definition head2'' {n : nat} (bs cs : bits (S n)) : bit * bit :=
  match bs in (bits n) return match n with
                              | 0   => IDProp
                              | S _ => bit * bit
                              end
  with
  | bnil => idProp
  | bcons b _ => 
    match cs in (bits n) return match n with
                                | 0   => IDProp
                                | S _ => bit * bit
                                end
    with
    | bnil => idProp
    | bcons c _ => (b,c)
    end
  end.
Print head2''. 

(* read me end PRINT ME ON TYPORA , Iain Moncrief, Martin Erwig, Christine Line, Iain Moncrief, Iain Moncrief, Christine Lin, Iain Moncrief, Martin Erwig, Eric Walkingshaw, Iain Moncrief *)


Fixpoint zip_with_bits {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n :=
  match 
  (* match bs in (bits n0) return match n0 with
                               | 0   => IDProp
                               | S _ => bit *)
Definition bits_head' {n : nat} (bs : bits (S n)) : bit.


Fixpoint zip_with_bits {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n :=
  match n with
  | 0 => match v1 in bits 0, v2 in bits 0 with
         | bnil, bnil => bnil
          end
  | S n' => 
    match v1 in bits (S n') return bits n with
    | @bcons m x xs => 
      match v2 in bits (S m) return bits (S n') with
      | bcons y ys => bcons (f x y) (zip_with_bits xs ys)
      end
    end
  end.
    match v1 in bits 0,v2 in bits 0 return bits 0 with
    | bnil , bnil => bnil
    end
  | S m => 
    match v1 in bits (S m), v2 in bits (S m) return bits n with
    | bcons x xs, bcons y ys => bcons (f x y) (zip_with_bits xs ys)
    end
  end.


Fixpoint zip_with_bits {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n :=
  match v1 return bits n with
  | bnil => 
    match v2 in bits 0 return bits 0 with
    | bnil => bnil
    end
  | @bcons m x xs => 
    match v2 in bits (S m) return bits n with
    | bcons y ys => bcons (f x y) (zip_with_bits xs ys)
    end
  end.
    match v1 in bits 0,v2 in bits 0 return bits 0 with
    | bnil , bnil => bnil
    end
  | S m => 
    match v1 in bits (S m), v2 in bits (S m) return bits n with
    | bcons x xs, bcons y ys => bcons (f x y) (zip_with_bits xs ys)
    end
  end.


Fixpoint zip_with_bits {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n :=
  match n with
  | 0 => 
    match v1 in bits 0,v2 in bits 0 return bits 0 with
    | bnil , bnil => bnil
    end
  | S m => 
    match v1 in bits (S m), v2 in bits (S m) return bits n with
    | bcons x xs, bcons y ys => bcons (f x y) (zip_with_bits xs ys)
    end
  end. 


  (* match v1,v2 with
  | bnil, _ => bnil
  | bcons x xs, bcons y ys => bcons (f x y) (zipWith xs ys)
  end. *)

Fixpoint zipWith {n : nat} (f : bit -> bit -> bit)
  (v1 : bits n) (v2 : bits n) : bits n :=
  match v1 in bits n return bits n -> bits n with
  | bnil => fun _ => bnil
  | @bcons m x xs => fun v2 =>
    match v2 in bits (S m) (*return bits n*) with
    | bnil => bnil
    | @bcons m y ys => bcons (f x y) (zipWith f xs ys)
    end
  end v2.

Definition bits_map2 {n : nat} (f : bit -> bit -> bit) (bs cs: bits n) : bits n :=
  from_list (zip_with f (to_list bs) (to_list cs)).


(* Fixpoint bits_zip_with {n : nat} 
                       (f : bit -> bit -> bit)
                       (bs cs : bits n) : bits n :=
  match bs, cs with
  | bnil, bnil => bnil
  | bcons b bs', bcons c cs' => bcons (f b c) (bits_zip_with f bs' cs')
  end. *)

Definition bits_zip_with_s {n : nat} 
                           (f : bit -> bit -> bit)
                           (bs cs : bits (S n)) : bits (S n) :=
  match bits_uncons2 bs cs with
  | ((b,bs'),(c,cs')) => bcons (f b c) (bits_zip_with f bs' cs')
  end.

Fixpoint bits_zip_with {n : nat} 
                       (f : bit -> bit -> bit)
                       (bs cs : bits n) : bits n :=
  match n as n with
  | 0 => bnil
  | S n' => match bits_uncons2 bs cs with
            | ((b,bs'),(c,cs')) => bcons (f b c) (bits_zip_with f bs' cs')
            end
  end.
  (* match bs in bits n return bits n -> bits n with
  | bnil => fun cs =>
    match cs with
    | bnil => bnil
    end
  | bcons b bs' => fun cs =>
    match cs with
    | bcons c cs' => bcons (f b c) (bits_zip_with f bs' cs')
    end
  end. *)

(*                       
  match n with
  | 0    => bnil
  | S n' => 
    match bs, cs in (bits (S n')) return (bits (S n')) with 
    | bcons b bs',bcons c cs' =>
      bcons (f b c) (bits_zip_with f bs' cs')
    end
  end. *)

Axiom helper : forall (n : nat), bits n.

Fixpoint bitwise_apply {n : nat} (op : bit_bin_op) (bs1 bs2 : bits n) : bits n :=
  match n (*as m return match m with
                      | 0 => bits 0
                      | S n' => bits n end*) with
  | 0 => bnil
  | S n' as m => bcons (op (bits_head n' bs1) (bits_head n' bs2)) (helper n')
  end
  and 
  (* match n return match n with 
                 | 0 => bits 0
                 | S n' => bits (S n')
                 end with *)
  
  


Fixpoint bitwise_apply (op : bit_bin_op) (n : nat) (bs1 bs2 : bits n) : bits n :=
  match bs1, bs2 with
  | bnil, bnil => bnil
  | bcons h1 t1, bcons h2 t2 =>
      bcons (op h1 h2) (bitwise_apply op _ t1 t2)
  end.


Fixpoint bitwise_apply (op : bit_bin_op) (n : nat) (bs1 bs2 : bits n) : bits n :=
  match n with
  | 0 => bnil
  | S n' => bcons (op (bits_head n' bs1) (bits_head n' bs2)) (bitwise_apply op n' (bits_tail n' bs1) (bits_tail n' bs2))
  end.
    (* match bs1, bs2 with
    | bcons b1 bs1', bcons b2 bs2' =>
      bcons (op b1 b2) (bitwise_apply op bs1' bs2')
    end *)
  (* Fixpoint bitwise_apply (op : bit_bin_op) (n : nat) (bs1 bs2 : bits (S n)) : bits (S n) :=
  bcons (op (bits_head n bs1) (bits_head n bs1)) (bitwise_apply op (bits_tail n bs1) (bits_tail n bs2)). *)
