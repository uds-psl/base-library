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

Tactic Notation "intros" "***" := repeat (intros ?).

Ltac fstep N := unfold N; fold N.

Inductive Lock : Prop -> Prop := L (P : Prop) (x : P) : Lock P.

Lemma do_Lock (x : Prop) : Lock x -> x.
Proof.
  firstorder. now destruct H. 
Qed.

Lemma do_unLock (x : Prop) : x -> Lock x.
Proof.
  firstorder. now econstructor.
Qed.

Tactic Notation "lock" := eapply do_Lock.
Tactic Notation "unlock" := eapply do_unLock.

Tactic Notation "lock" ident(H) := eapply do_unLock in H.
Tactic Notation "unlock" ident(H) := eapply do_Lock in H.

Tactic Notation "locked" tactic(t) := lock; t; unlock.

Tactic Notation "unlock" "all" := repeat match goal with
                                         | [ H : Lock _ |- _] => unlock H
                                         | [ |- Lock _ ] => unlock
                                        end.
(* From Program.Tactics *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

Ltac destruct_pairs := repeat (destruct_one_pair).

Require Export AutoIndTac.

