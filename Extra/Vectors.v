Require Export Vector VectorDef.

Delimit Scope vector_scope with vector_scope.

Notation "[||]" := (nil _) : vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.
                        
Notation " [| x |] " := ((x ::: [||])%vector_scope) : vector_scope.
Notation " [| x ; y ; .. ; z |] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]").

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
