Require Import Shared.Prelim Shared.Tactics.Tactics Shared.EqDec.
Require Import Coq.Vectors.Fin Coq.Vectors.Vector.


Tactic Notation "dependent" "destruct'" constr(V) :=
  match type of V with
  | Vector.t ?Z 0 =>
    revert all except V;
    pattern V; revert V;
    eapply case0; intros
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

Tactic Notation "dependent" "destruct" constr(V) :=
  match type of V with
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Notation "[||]" := (nil _) : vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.

Notation " [| x |] " := (x ::: [||]) : vector_scope.
Notation " [| x ; y ; .. ; z |] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.


Lemma Vector_replace_nth X n (v : Vector.t X n) i (x : X) :
  (Vector.replace v i x) [@i] = x.
Proof.
  induction i; dependent destruct v; cbn; auto.
Qed.

Lemma Vector_replace_nth2 X n (v : Vector.t X n) i j (x : X) :
  i <> j -> (Vector.replace v i x) [@j] = v[@j].
Proof.
  revert v. pattern i, j. revert n i j.
  eapply Fin.rect2; intros; try congruence.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert g f H H0. pattern v. revert n v.
    eapply Vector.caseS. firstorder congruence.
Qed.

Lemma destruct_vector_nil (X : Type) :
  forall v : Vector.t X 0, v = [||].
Proof.
  now apply case0.
Qed.

Lemma destruct_vector_cons (X : Type) (n : nat) :
  forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }}.
Proof.
  revert n. apply caseS. eauto.
Qed.

Ltac existT_eq :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H
  end.

Ltac existT_eq' :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H
  end.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) :
  In y (x ::: xs) -> x = y \/ In y xs.
Proof.
  intros H. inv H; existT_eq'; tauto.
Qed.

(* Destruct a vector of known size *)
Ltac destruct_vector :=
  repeat match goal with
         | [ v : Vector.t ?X 0 |- _ ] =>
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_nil X v) as H;
           subst v
         | [ v : Vector.t ?X (S ?n) |- _ ] =>
           let h  := fresh "h" in
           let v' := fresh "v'" in
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_cons X n v) as (h&v'&H);
           subst v; rename v' into v
         end.

Section In_nth.
  Variable (A : Type) (n : nat).

  Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) :
    Vector.nth v i = x -> Vector.In x v.
  Proof.
    induction n; cbn in *.
    - inv i.
    - dependent destruct v. dependent destruct i; cbn in *; subst; econstructor; eauto.
  Qed.

  Lemma vect_nth_In' (v : Vector.t A n) (x : A) :
    Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
  Proof.
    induction n; cbn in *.
    - inversion 1.
    - dependent destruct v. inv H.
      + apply EqdepFacts.eq_sigT_eq_dep in H3. induction H3. exists Fin.F1. auto.
      + apply EqdepFacts.eq_sigT_eq_dep in H3. induction H3. specialize (IHn0 _ H2) as (i&<-). exists (Fin.FS i). auto.
  Qed.

End In_nth.

Section tabulate_vec.
  Variable X : Type.

  Fixpoint tabulate (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
  Proof.
    destruct n.
    - apply Vector.nil.
    - apply Vector.cons.
      + apply f, Fin.F1.
      + apply tabulate. intros m. apply f, Fin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) :
    Vector.nth (tabulate f) m = f m.
  Proof.
    induction m.
    - cbn. reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Qed.

  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate (n := n) f) <-> exists i : Fin.t n, x = f i.
  Proof.
    split.
    {
      revert f x. induction n; intros f x H.
      - cbn in *. inv H.
      - cbn in *. apply In_cons in H as [ <- | H ].
        + eauto.
        + specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH). eauto.
    }
    {
      intros (i&Hi). induction i; cbn in *; subst; econstructor; eauto.
    }
  Qed.

End tabulate_vec.

(*
Lemma vec_replace_nth X x n (t : Vector.t X n) (i : Fin.t n) :
  x = Vector.nth (Vector.replace t i x) i.
Proof.
  induction i; dependent destruct t; simpl; auto.
Qed.

Lemma vec_replace_nth_nochange X x n (t : Vector.t X n) (i j : Fin.t n) :
  Fin.to_nat i <> Fin.to_nat j -> Vector.nth t i = Vector.nth (Vector.replace t j x) i.
Proof.
  revert j. induction i; dependent destruct t; dependent destruct j; simpl; try tauto.
  apply IHi. contradict H. cbn. now rewrite !H.
Qed.
 *)


Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.


(* Generate instances of Fin.t *)
Tactic Notation "getFin" constr(i) constr(j) :=
  apply (Fin.of_nat_lt (ltac:(omega) : i < j) : Fin.t j).

Tactic Notation "getFin'" int(i) :=
  do i apply Fin.FS; eapply Fin.F1.

(*
Section Test.
  Compute ltac:(getFin 3 4).
  Compute ltac:(getFin' 3) : Fin.t 4.
End Test.
*)