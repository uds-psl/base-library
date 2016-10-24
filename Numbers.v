Require Import Base.

(** ** Numbers **)

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D. revert x.
  enough (forall n y, sigma y < n -> p y) by eauto.
  intros n. induction n; intros y E. 
  - exfalso; omega.
  - apply D. intros x F.  apply IHn. omega.
Qed.

Arguments size_recursion {X} sigma {p} _ _.

Section Iteration.
  Variables (X: Type) (f: X -> X).

  Fixpoint it (n : nat) (x : X) : X := 
    match n with
      | 0 => x
      | S n' => f (it n' x)
    end.

  Lemma it_ind (p : X -> Prop) x n :
    p x -> (forall z, p z -> p (f z)) -> p (it n x).
  Proof.
    intros A B. induction n; cbn; auto.
  Qed.

  Definition FP (x : X) : Prop := f x = x.

  Lemma it_fp (sigma : X -> nat) x :
    (forall n, FP (it n x) \/ sigma (it n x) > sigma (it (S n) x)) ->
    FP (it (sigma x) x).
  Proof.
    intros A.
    assert (B: forall n, FP (it n x) \/ sigma x >= n + sigma (it n x)).
    { intros n; induction n; cbn.
      - auto. 
      - destruct IHn as [B|B].
        + left. now rewrite B. 
        + destruct (A n) as [C|C].
          * left. now rewrite C. 
          * right. cbn in C. omega. }
    destruct (A (sigma x)), (B (sigma x)); auto; exfalso; omega.
  Qed.
End Iteration.
