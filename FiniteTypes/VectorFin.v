Require Import Shared.FiniteTypes.FinTypes.
Require Import Shared.Vectors.Vectors.
Require Import Shared.Vectors.VectorDupfree.

Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
  pose (enum := tabulate (fun i : Fin.t n => i)).
  pose (enum' := Vector.to_list enum).
  constructor 1 with (enum := enum').
  intros x. cbn in x.
  eapply dupfreeCount.
  - subst enum'. eapply tolist_dupfree. eapply dupfree_tabulate_functional; eauto.
  - eapply tolist_In. subst enum. eapply in_tabulate. eauto.
Qed.