Require Import FinTypes Vector.

Instance eq_dec_vector (X : Type) `{eq_dec X} n : eq_dec (Vector.t X n).
Proof.
  eapply Vector.eq_dec with (A_beq := fun x y => Decb (x = y)). firstorder. now decide (x = y).
Defined.

Fixpoint all_vectors (X : Type) (A : list X) n : list (Vector.t X n) :=
  match n with
    0 => [Vector.nil X]
  | S n' => concat (List.map (fun a => (List.map (fun v => cons _ a _ v) (all_vectors A n'))) A)
  end.

Lemma vectors_enum_ok (X : finType) n (v : Vector.t X n):
  count (undup (all_vectors (elem X) n)) v = 1.
Proof.
  apply dupfreeCount.
  -apply dupfree_undup.
  -rewrite undup_id_equi. induction v;cbn. tauto.
   rewrite in_concat_iff. eexists; split; rewrite in_map_iff; eauto. 
Qed.

Instance fintype_vector (X : finType) n : finTypeC (EqType (Vector.t X n)).
Proof.
  econstructor. apply vectors_enum_ok. 
Qed.

Hint Extern 4 (finTypeC (EqType (Vector.t _ _))) => eapply fintype_vector : typeclass_instances.
