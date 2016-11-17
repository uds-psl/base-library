Ltac inv H := inversion H; subst; try clear H.

Tactic Notation "destruct" "_":=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X 
  end.

Tactic Notation "destruct" "_" "eqn" ":" ident(E)   :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:E
  end.

Tactic Notation "destruct" "*" :=
  repeat destruct _.

Tactic Notation "destruct" "*" "eqn" ":" ident(E) :=
  repeat (let E := fresh E in destruct _ eqn:E; try progress inv E); try now congruence.

Tactic Notation "destruct" "*" "eqn" ":" "_" := destruct * eqn:E.

Ltac fstep N := unfold N; fold N.

Inductive Lock : Prop -> Prop := L (P : Prop) (x : P) : Lock P.

Lemma Lock_eq (x : Prop) : Lock x <-> x.
Proof.
  firstorder. now destruct H. now econstructor.
Qed.

Tactic Notation "lock" "firstorder" := eapply Lock_eq; firstorder; match goal with [ |- Lock _] => eapply Lock_eq end.
