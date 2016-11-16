Require Export Vector VectorDef.

Import VectorDef.VectorNotations.

Lemma Vector_replace_nth X n (v : Vector.t X n) i (x : X) :
  (Vector.replace v i x) [@i] = x.
Proof.
  induction i.
  - cbn. revert x. pattern v. revert n v. eapply Vector.caseS.
    cbn. reflexivity.
  - cbn. revert x i  IHi. pattern v. revert n v. eapply Vector.caseS.
    intros. cbn. eapply IHi.
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
