Require Import Unicode.Utf8.

Require Import Psatz.
Require Import Coq.Arith.Arith.

Import ZArith.

Open Scope Z_scope.

Lemma neg_b_min_a_a_min_b: forall a b, -(b - a) = a - b.
Proof.
  intros a b.
  induction a; induction b; try lia.
Qed.


Lemma my_Z_sub_diag : forall n : Z, n - n = 0.
Proof.
  induction n; simpl.
  reflexivity.
  all: induction p.
  all: simpl.
  

Lemma congruence_divides : ∀ a b n : Z, n <> 0 -> (a mod n) = (b mod n) <-> (n | (b - a)).
Proof.
  intros a b n Hn.
  split.
  - (* -> direction *)
    intros H.
    assert (H1: (a - b) mod n = 0).
    {
      rewrite Zminus_mod.
      rewrite H.
      rewrite Z.sub_diag.
      
      apply Z.mod_0_l.
    }
    apply Z.mod_divide in H1; auto.
    apply Z.divide_opp_r.
    simpl.
    rewrite neg_b_min_a_a_min_b.
    assumption.
  - (* <- direction *)
    intros H.
    destruct H as [k Hk].
    assert (H1: b = k * n + a).
    { lia. }
    rewrite H1.
    apply eq_sym.
    rewrite Z.add_comm.
    rewrite Z_mod_plus_full.
    reflexivity.
Qed.


Lemma mod_def :
  forall (n a b : Z),
    a mod n = b mod n <-> (n | (a - b)). 

Proof.
  intros n a b.
  split.
  - intros H.
    unfold Z.modulo in H.
    simpl.
   induction a. 



  destruct b.