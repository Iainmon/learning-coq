


Require Import Unicode.Utf8.


Theorem my_theorem:
  forall (A : Type) (x y : A),
    x = y <-> (forall P : A -> Prop, P x <-> P y).
Proof.
  intros A x y.
  split.
  - intros H1. (* Show Proof. *)
    rewrite H1.
    intros P.
    split; intros; assumption.
  - intros H2.
    apply H2.
    reflexivity.
Qed.


Lemma equal_f : 
  forall {A B : Type} {f g : A -> B},
    f = g -> forall x, f x = g x.
Proof.
  intros A B.
  intros f g.
  intros H.
  intros x.
  rewrite H.
  reflexivity.
Qed.

(* same proof as above? *)
Lemma equal_f_dep : 
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
    f = g -> forall x, f x = g x.
Proof.
  intros A B.
  intros f g.
  intros H.
  intros x.
  rewrite H.
  reflexivity.
Qed.


Axiom fun_ext_dep :
  forall {A : Type} {B : A -> Type} {f g : forall a, B a},
    (forall x, f x = g x) -> f = g.


Theorem fun_ext:
  forall {A B : Type} {f g : A -> B},
    (forall a, f a = g a) -> f = g.
Proof.
  intros A B.
  intros f g.
  apply fun_ext_dep.
Qed.

Definition add (n m : nat) : nat := n + m.
About add.











Goal forall (A B : Type) (f g : A -> B),
  (forall a, f a = g a) -> g = f. 
Proof.
  intros A B f g H.
  apply my_theorem.

