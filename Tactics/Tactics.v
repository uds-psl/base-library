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



(* Show the non-dependent hypothesis of a hypothesis that is a implication and specialize it *)
Tactic Notation "spec_assert" hyp(H) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H'; [ | specialize (H H'); clear H']
  end.

Tactic Notation "spec_assert" hyp(H) "as" simple_intropattern(p) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H'; [ | specialize (H H') as p; clear H']
  end.

Tactic Notation "spec_assert" hyp(H) "by" tactic(T) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H' by T; specialize (H H'); clear H'
  end.


Tactic Notation "spec_assert" hyp(H) "as" simple_intropattern(p) "by" tactic(T) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H' by T; specialize (H H') as p; clear H'
  end.


Require Export AutoIndTac.