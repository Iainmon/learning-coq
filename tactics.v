Ltac know a b new_hyp :=
  match goal with
  | [H : a = b |- _] => pose proof H as new_hyp
  | [H : b = a |- _] => pose proof (eq_sym H) as new_hyp
  end.

Ltac derive_equality t u :=
    match goal with
    | [ H: t = u |- _ ] => idtac (* Equality already in context *)
    | _ =>
        let H := fresh "H" in
        tryif (assert (H : t = u) by (congruence || auto))
        then idtac
        else idtac (* Do nothing if equality cannot be deduced *)
    end.

Require Import List.
Import ListNotations.
Ltac derive_equalities_rec eqs :=
    match eqs with
    | nil => idtac
    | (?t = ?u) :: ?rest =>
        derive_equality t u;
        derive_equalities_rec rest
    end.

Tactic Notation "derive_equalities" constr(eq_list) :=
derive_equalities_rec eq_list.

Lemma example (a b c d : nat) (H1 : a = b) (H2 : b = c) (H3 : c = d) : a = d.
Proof.
    (* derive_equalities ((a = b) :: nil). *)
  derive_equalities [a = b; b = c; c = d; a = d].

  (* Now, a = d is available in the context *)
  exact (eq_trans H1 (eq_trans H2 H3)).
Qed.
