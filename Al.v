

(* Inductive Witness : Type -> X -> Prop := 
  | witness : forall (X : Type), exists (a : X), Witness X a.  *)

(* Search inhabited. *)

(* 
Inductive inhabited (X : Type) : Prop := 
  inhabits : X -> inhabited X. 
*)

Definition inhabited (X : Type) := X.

(* Axiom inhabited_witness : forall X : Type, inhabited X -> X. *)

Definition nempty (X : Type) : Type
  := inhabited X.

Definition relation (X : Type) : Type
  := X -> X -> Prop.

Definition total {X : Type} (R : relation X) : Prop
  := forall a : X, exists b : X, R a b.
  
Definition seq (X : Type) : Type
  := nat -> X.


Lemma exists_inhabited_P : 
  forall {X : Type} (P : X -> Prop),
    (exists a, P a) -> 
      inhabited X.
Proof.
  intros X P H.
  destruct H.
  apply inhabits.
  exact x.
Qed.

Lemma exists_inhabited_direct : 
  forall {X : Type},
    (exists (a : X), True) -> 
      inhabited X.
Proof.
  intros X.
  intros H.
  destruct H as [a H1].
  apply inhabits.
  exact a.
Qed.

Lemma exists_inhabited : 
  forall {X : Type},
    (exists (a : X), True) <-> 
      inhabited X.
Proof.
  intros X.
  split.
  - intros H.
    destruct H as [a H1].
    apply inhabits.
    exact a.
  - intros H.
    inversion H as [a].
    exists a.
    exact I. 
Qed.


Lemma test: nempty nat.
Proof.
  exact (inhabits 0).
Qed.

Lemma seq_implies_nempty:
  forall (X : Type),
    seq X -> nempty X.
Proof.
  intros X.
  intros sq.
  unfold seq in sq.
  unfold nempty in *.
  apply inhabits.
  apply sq.
  apply 0.
  Show Proof.
Qed.

Lemma nempty_witness:
  forall {X : Type}, 
  nempty X -> X.
Proof.
  intros X H.
  unfold nempty in H.
  inversion H.
  destruct H as [a I].

  unfold nempty in H.
  simpl in H.
  auto.
  intros [x _].


Lemma witness_lemma:
  forall (X : Type),
    (exists a : X, Witness a) <-> (exists a : X, True).
Proof.


  inversion H.
  exact ?x.
  destruct H.




Lemma nempty_implies_seq:
  forall (X : Set),
    nempty X -> seq X.
Proof.
  intros X.
  intros H1.
  unfold nempty in H1.
  intros n.
  destruct H1 as [a _].

Definition ax_dependent_choice : 
  forall (X : Set),
    nempty X ->
      forall (R : relation X),
        total R -> 
          exists (s : seq X),
            forall n : nat,
              R (s n) (s (n + 1)).
Proof.





