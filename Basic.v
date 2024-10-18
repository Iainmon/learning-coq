Ltac save h1 h2 := 
  (*pose proof h1 as h2*)
  let t := type of h1 in 
    assert (h2 : t) by (exact h1).

Tactic Notation "save" constr(h1) "as" ident(h2) := 
  save h1 h2.


(* Ltac replace_equivalent a b p :=
  let at := type of a in
  let bt := type of b in
  match type of p with
  | at <-> bt => *)

Require Import List.
Import ListNotations.

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | x :: l' => (f x) :: (map f l')
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' => drop n' (tail l)
  end.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x = x' \/ In x l'
  end.

(* Inductive elementhood {A : Type} : A -> list A -> Prop :=
  | element_of : forall a l, In a l -> elementhood a l. *)

Inductive element {A : Type} (x : A) : list A -> Prop :=
  | element_here : forall l, element x (x :: l)
  | element_there : forall y l, element x l -> element x (y :: l).

Notation "a '∈' l" := (element a l) (at level 70).

Theorem in_equiv: 
  forall (A : Type) (x : A) (l : list A),
    In x l <-> x ∈ l.
Proof.
  intros A x l.
  split.  
  - intros H1. 
    induction l as [| y l' IH].
    + contradiction.
    + cbn in H1.
      destruct H1 as [ H2 | H3 ].
      * rewrite H2.
        apply element_here.
      * apply IH in H3.
        apply element_there.
        assumption.
  - intros H1.
    induction l as [| y l' IH].
    + inversion H1.
    + simpl. inversion H1.
      * left. reflexivity.
      * right. apply IH in H0. assumption.
Qed.

Lemma in_ident: 
  forall (A : Type) (a : A) (l : list A),
    In a l -> In a (a :: l).
Proof.
  intros A a.
  intros l.
  intros H.
  destruct l.
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
Qed.

Lemma if_In_then_drop_head:
  forall (A : Type) (l : list A) (x : A),
    In x l -> 
      exists n l', drop n l = x :: l'.
Proof.
  intros A l x.
  intros H1.
  induction l.
  - simpl in H1. contradiction.
  - simpl in H1.
    destruct H1 as [ H1_1 | H1_2 ].
    + rewrite <- H1_1.
      exists 0,l.
      reflexivity.
    + apply IHl in H1_2 as H2.
      save H2 as H3.
      destruct H3 as [m [l1 H4]].
      exists (S m).
      exists l1.
      simpl.
      assumption.
Qed.

Lemma In_map: 
  forall (A B : Type) (f : A -> B) l x,
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  intros H1.
  generalize dependent l.
  induction l.
  (* all: try (unfold In; left; auto). *)
  - unfold In. simpl. contradiction.
  - intros H2. simpl.
    save H2 as H3. simpl in H3.
    destruct H3 as [ H4 | H5 ].
    + left. rewrite H4. reflexivity.
    + right. apply IHl in H5. assumption.
Qed.

(* Lemma element_decidable *)
Lemma element_map:
  forall (A B : Type) (f : A -> B) l x,
    x ∈ l -> (f x) ∈ (map f l).
Proof.
  intros A B f.
  intros l.
  intros x.
  generalize dependent l.
  induction l.
  - intros H1.
    inversion H1.
  - intros H1.
    simpl.
    inversion H1.
    + rewrite <- H0.
      apply element_here.
    + apply IHl in H0.
      apply element_there. 
      assumption.
Qed.  

Lemma in_app_iff: 
  forall (A : Type) (x : A) l1 l2,
    In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros A x l1 l2.
  split; intros H1.
  - induction l1.
    + simpl in H1. right. assumption.
    + simpl in H1.
      destruct H1 as [H2 | H3].
      * left. rewrite H2. simpl. left. reflexivity.
      * save IHl1 as H4.
        apply H4 in H3 as H5.
        destruct H5 as [H6 | H7].
        -- left. simpl. right. assumption.
        -- right. assumption.
  - induction l1; destruct H1 as [H2 | H3]; simpl.
    + simpl. contradiction.
    + assumption.
    + destruct H2.
      -- left. assumption.
      -- assert (H3 : In x l1 \/ In x l2).
          { left. assumption. }
        apply IHl1 in H3. right. assumption. 
    + right.
      assert (H4: In x l1 \/ In x l2).
        { right. assumption. }
     apply IHl1. right. assumption.
Qed.

Lemma in_split: 
  forall (A : Type) (x : A) l,
    In x l -> 
      exists l1 l2, 
        l = l1 ++ x :: l2.
Proof.
  intros A x l.
  intros H1.
  induction l as [| x' l' IHl'].
  - unfold In in H1.
    contradiction.
  - unfold In in H1.
    destruct H1 as [H1_1 | H1_2].
    + exists [].
      exists l'.
      simpl.
      rewrite H1_1.
      reflexivity.
    + assert (H4 : In x l').
        { apply H1_2. }
      pose proof (IHl' H4) as H5.
      pose proof H5 as H6.
      destruct H5 as [l3 [l4 H5]].
      exists (x' :: l3).
      exists l4.
      simpl.
      rewrite H5.
      reflexivity.
Qed.

Lemma in_find:
  forall (A : Type) (l : list A),
    forall x, In x l <-> exists a, In a l /\ x = a.
Proof.
  intros A l.
  intros x.
  split.
  - intros H1.
    induction l as [| y l' IHl'].
    + simpl in H1. contradiction.
    + simpl in H1.
      destruct H1 as [H2 | H3].
      * exists y.
        split.
        -- left. reflexivity.
        -- rewrite H2. reflexivity.
      * apply IHl' in H3.
        destruct H3 as [a [H4 H5]].
        exists a.
        split.
        -- right. assumption.
        -- assumption.
  - intros H1.
    induction l as [| y l' IHl'].
    + simpl.
      destruct H1 as [a [H2 H3]].
      contradiction.
    + simpl.
      destruct H1 as [a [H2 H3]].
      destruct H2 as [H4 | H5].
      * rewrite H4 in H3.
        left. assumption.
      * right. apply IHl'.
        exists a.
        split.
        -- assumption.
        -- assumption.
Qed.

Lemma in_map_iff:
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H1.
    induction l as [| x l' IHl'].
    + simpl in H1. contradiction.
    + simpl in H1.
      apply in_app_iff in H1.
      destruct H1 as [H2 | H3].
      * exists x.
        split.
        -- simpl in H2. inversion H2.
           reflexivity.
        -- left. reflexivity.
      * apply IHl' in H3.
        destruct H3 as [a [H4 H5]].
        exists a.
        split.
        -- assumption.
        -- right. assumption.
  - intros H1.
    induction l as [| x l' IHl'].
    + simpl.
      destruct H1 as [a [H2 H3]].
      contradiction.
    + simpl.
      destruct H1 as [a [H2 H3]].
      destruct H3 as [H4 | H5].
      * rewrite H4 in H2.
        left. rewrite H2. reflexivity.
      * right. apply IHl'.
        exists a.
        split.
        -- assumption.
        -- assumption.


Definition subseq {A : Type} (l1 l2 : list A) : Prop :=
  forall x, x ∈ l1 -> x ∈ l2.

Notation "l1 '⊆' l2" := (subseq l1 l2) (at level 70).

Lemma subseq_refl: 
  forall (A : Type) (l : list A),
    l ⊆ l.
Proof.
  intros A l.
  unfold subseq.
  intros x.
  intros H1.
  assumption.
Qed.



Lemma subseq_trans:
  forall (A : Type) (l1 l2 l3 : list A),
    l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3.
Proof.
  intros A.
  intros l1 l2 l3.
  intros H1.
  intros H2.
  simpl in H1.
  unfold subseq in H1, H2.
  unfold subseq.
  (* auto. *)
  intros x H3.
  apply H1 in H3.
  apply H2 in H3.
  assumption.
Qed.

Lemma subseq_empty:
  forall (A : Type) (l : list A),
    [] ⊆ l.
Proof.
  intros A l.
  unfold subseq.
  intros x H.
  inversion H.
Qed.

Lemma subseq_map_image:
  forall (A B : Type) (f : A -> B) (l1 l2 : list A),
    l1 ⊆ l2 -> forall (a : A), a ∈ l1 -> f a ∈ map f l2.
Proof.
  intros A B f.
  intros l1 l2.
  intros H1.
  intros a.
  intros H2.
  save H2 as H3.
  apply (element_map A B f) in H3.
  unfold subseq in H1.
  pose proof (H1 a H2) as H4.
  apply (element_map A B f) in H4.
  assumption.
Qed.


Lemma subseq_map_image_2:
  forall (A B : Type) (l1 l2 : list A) (f : A -> B),
    l1 ⊆ l2 -> map f l1 ⊆ map f l2.
Proof.
  intros A B.
  intros l1 l2.
  intros f.
  unfold subseq.
  intros H1.
  intros y H2.
  About in_map_iff.
  apply In_map_iff in H2.



  replace in_equiv in (context [?x ∈ l1]).
  unfold subseq in H1.
  unfold subseq.
  intros b.
  intros H2.
  inversion H2.
  -  
  induction l1.
  - simpl in H2. inversion H2.
  - simpl in H2.
    destruct H2.
    + 
    inversion H2.

  induction l1.
  - intros H1. simpl. apply subseq_empty.
  - intros H1.
    unfold subseq in H1.
    assert (H2 : a ∈ a :: l1).
      { apply (element_here a). }

    pose proof (H1 a H2) as H3.

    intros b.
    intros H4.
    apply element_map.
    pose proof (element_map )
    intros b.
    intros H2. 
  
  


  intros H1.
  unfold subseq.
  induction l1.
  - simpl. apply subseq_empty.
  - unfold subseq.
    save H1 as H2.

    unfold subseq in H2.
    pose proof (H2 a) as H3.
    assert (H4: a ∈ a :: l1).
      { apply element_here. }
    pose proof (H2 a H4) as H5.

    inversion 
    intros b.
    intros H3.
    inversion 
    (* simpl in H3. *)
    inversion H3.
    + simpl. rewrite <- H4 in H3.
  
  simpl. 
  unfold subseq.
  intros y.
  unfold subseq in H1.
  induction l1.

  (* intros A B.
  intros l1 l2.
  intros f.
  intros H1.
  unfold subseq.
  intros y.
  unfold subseq in H1.
  induction l1. *)



Definition seteq {A : Type} (l1 l2 : list A) : Prop :=
  forall l1 ⊆ l1 /\ l2 ⊆ l1.

Definition seteq_subset_in_equiv:
  forall (A : Type) (l1 l2 : list A)

Lemma concat_union:
  forall (A : Type) (l1 l2 : list A)

Theorem pigeonhole_principle:
  forall (A : Type)
