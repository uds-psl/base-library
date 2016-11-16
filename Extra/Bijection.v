
(** 

  - Dimitri Hendriks 2013-10-09

  - http://www.cs.vu.nl/~diem/coq/calkin-wilf/bijection.html

 *)

Set Implicit Arguments.

Section bijections.

  Variables A B : Type.

  Definition injective (f : A -> B) := forall x y : A, f x = f y -> x = y.

  Definition surjective (f : A -> B) := forall y : B, exists x : A, f x = y.

  Definition bijective (f : A -> B) : Type := injective f /\ surjective f.

  Definition left_inverse (f : A -> B) (f' : B -> A) :=
    forall x : A, f' (f x) = x.

  Definition right_inverse (f : A -> B) (f' : B -> A) :=
    forall y : B, f (f' y) = y.

  Definition inverse f f' :=
    left_inverse f f' /\  right_inverse f f'.

  Lemma left_inv_inj f f' : left_inverse f f' -> injective f.
  Proof.
    intros H x y H0.
    rewrite <- (H x).
    rewrite H0.
    apply H.
  Qed.

  Lemma right_inv_surj f f' : right_inverse f f' -> surjective f.
  Proof.
    intros H y.
    rewrite <- (H y).
    unfold right_inverse in H.
    exists (f' y). reflexivity.
  Qed.

  Lemma inv2bij f f' : inverse f f' -> bijective f.
  Proof.
    intros [H1 H2].
    econstructor. eapply (left_inv_inj H1). eapply (right_inv_surj H2).
  Qed.

End bijections.
