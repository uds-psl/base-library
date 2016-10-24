Require Export Prelim.

Export ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).
Hint Unfold equi.

Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end.

(** ** Lists *)

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (cbn; omega).
  apply C. now rewrite B.
Qed.

(** *** Decisions for lists *)

Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(* Certifying find *)

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  destruct (find (fun x => Dec (p x)) A) eqn:E.
  - apply find_some in E. firstorder.
  - right. intros. eapply find_none in E; eauto.
Qed.

Arguments cfind {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (~ p x)) A) eqn:Eq.
  - apply find_some in Eq as [H1 H0 %Dec_true]; right; auto. 
  - left. intros x E. apply find_none with (x := x) in Eq. apply dec_DN; auto. auto.
Qed.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (p x)) A) eqn:Eq. (* New: eta expansion needed *)
  - apply find_some in Eq as [H0 H1 %Dec_true]. firstorder. (* New: Need firstorder here *)
  - right. intros [x [E F]]. apply find_none with (x := x) in Eq; auto. eauto. (* New: Why can't auto solve this? *)
Qed.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (find (fun x => Dec (p x)) A) eqn:Eq.
  + apply find_some in Eq as [? ?%Dec_true]. eauto.
  + exfalso. apply E. intros. apply find_none with (x := x) in Eq;  eauto. 
Qed.

Lemma list_exists_not_incl (X: eqType) (A B : list X) :
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.



(** *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

Hint Resolve in_eq in_nil in_cons in_or_app.

Section Membership.
  Variable X : Type.
  Implicit Types (x y: X) (A B: list X).

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    cbn. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    cbn. intros [[]|D] E; congruence. 
  Qed.

  Lemma not_in_cons x y A :
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intuition; subst; auto.
  Qed.

(** *** Disjointness *)

  Definition disjoint A B :=
    ~ exists x, x el A /\ x el B.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split.
    - intros D x E F. apply D. exists x. auto.
    - intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    firstorder.
  Qed.
  
  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split.
    - intros D. split.
      + intros E. apply D. eauto.
      + intros [y [E F]]. apply D. eauto.
    - intros [D E] [y [[F|F] G]]. 
      + congruence.
      + apply E. eauto.
  Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split.
    - intros D. split.
      + intros [x [E F]]. eauto 6.
      + intros [x [E F]]. eauto 6.
    - intros [D E] [x [F G]]. 
      apply in_app_iff in F as [F|F]; eauto.
  Qed.

End Membership.

Hint Resolve disjoint_nil disjoint_nil'.

(** *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

Hint Resolve incl_nil.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_sing x A y :
    x::A <<= [y] -> x = y /\ A <<= [y].
  Proof.
    rewrite incl_lcons. intros [D E].
    apply in_sing in D. auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]; congruence. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** *** Setoid rewriting with list inclusion and list equivalence *)

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.
  Proof.
    auto.
  Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof.
    auto.
  Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof.
    split; intros z; cbn; tauto.
  Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.
  Proof. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x]. 
  Proof. 
    split; intros y; cbn.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
  
End Equi.

(** *** Filter *)

Section Filter.
  Variable X : Type.
  Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
  
  Fixpoint filter p A : list X :=
    match A with
    | nil => nil
    | x::A' => if p x then x :: filter p A' else filter p A'
    end.

  Lemma in_filter_iff x p A :
    x el filter p A <-> x el A /\ p x.
  Proof. 
    induction A as [|y A]; cbn.
    - tauto.
    - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto.
  Qed.

  Lemma filter_incl p A :
    filter p A <<= A.  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono p A B :
    A <<= B -> filter p A <<= filter p B.
  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id p A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:E.
      + f_equal; auto.
      + exfalso. apply bool_Prop_false in E. auto.
  Qed.

  Lemma filter_app p A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; cbn.
    - reflexivity.
    - rewrite IHA. destruct (p y); reflexivity.  
  Qed.

  Lemma filter_fst p x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_fst' p x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_pq_mono p q A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
  Proof. 
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_pq_eq p q A :
    (forall x, x el A -> p x = q x) -> filter p A = filter q A.
  Proof. 
    intros C; induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:D, (q x) eqn:E.
      + f_equal. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + auto.
  Qed.

  Lemma filter_and p q A :
    filter p (filter q A) = filter (fun x => p x && q x) A.
  Proof.
    induction A as [|x A]; cbn. reflexivity.
    destruct (p x) eqn:E, (q x); cbn;
      try rewrite E; now rewrite IHA.
  Qed.

  Lemma filter_comm p q A :
    filter p (filter q A) = filter q (filter p A).
  Proof.
    rewrite !filter_and. apply filter_pq_eq.
    intros x _. now destruct (p x), (q x).
  Qed.
  
End Filter.

(** *** Element removal *)

Section Removal.
  Variable X : eqType.
  Implicit Types (x y: X) (A B: list X).

  Definition rem A x : list X :=
    filter (fun z => Dec (z <> x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros E y F. decide (x=y) as [[]|]; auto using rem_neq.
  Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    unfold rem; rewrite filter_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
    intros [[]|E]; decide (x=y) as [[]|D]; 
    eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    apply filter_comm.
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros E. unfold rem. rewrite filter_fst; auto.
  Qed.

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros D. apply filter_id. intros y E.
    apply Dec_reflect. congruence.
  Qed.

  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros D. rewrite <- rem_equi. apply equi_push, D.
  Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros D E y F. apply in_rem_iff.
    intuition; subst; auto. 
  Qed.

End Removal.

Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr.

(** *** Cardinality *)

Section Cardinality.
  Variable X : eqType.
  Implicit Types A B : list X.

  Fixpoint card A :=
    match A with
      | nil => 0
      | x::A => if Dec (x el A) then card A else 1 + card A
    end.

  Lemma card_cons x A :
    x el A -> card (x::A) = card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.

  Lemma card_cons' x A :
    ~ x el A -> card (x::A) = 1 + card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.
  
  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros D. 
    induction A as [|y A].
    - contradiction D.
    - decide (y = x) as [->|H].
      + clear D. rewrite rem_fst.
        cbn. decide (x el A) as [H1|H1].
        * auto.
        * now rewrite (rem_id H1).
      + assert (x el A) as H1 by (destruct D; tauto). clear D.
        rewrite (rem_fst' _ H). specialize (IHA H1).
        simpl card at 2. 
        decide (y el rem A x) as [H2|H2].
        * rewrite card_cons. exact IHA.
          apply in_rem_iff in H2. intuition.
        * rewrite card_cons'. now rewrite IHA.
          contradict H2.  now apply in_rem_iff.
  Qed.
  
  Lemma card_not_in_rem A x :
    ~ x el A -> card A = card (rem A x).
  Proof.
    intros D; rewrite rem_id; auto.
  Qed.

  Lemma card_le A B :
    A <<= B -> card A <= card B.
  Proof.
  revert B. 
  induction A as [|x A]; intros B D; cbn.
  - omega.
  - apply incl_lcons in D as [D D1].
    decide (x el A) as [E|E].
    + auto.
    + rewrite (card_in_rem D).
      enough (card A <= card (rem B x)) by omega.
      apply IHA. auto.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.
  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. omega.
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof.
    rewrite (card_eq (rem_equi x A)). cbn.
    decide (x el rem A x) as [D|D].
    - exfalso. apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof.
    destruct A as [|x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. omega.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.
  Proof.
    intros D.
    decide (B <<= A) as [E|E].
    - exfalso. apply card_le in E. omega.
    - apply list_exists_not_incl; auto.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof.
    revert B. 
    induction A as [|x A]; cbn; intros B D E.
    - symmetry in E. apply card_0 in E. now rewrite E.
    - apply incl_lcons in D as [D D1].
      decide (x el A) as [F|F].
      + rewrite (IHA B); auto.
      + rewrite (IHA (rem B x)).
        * symmetry. apply rem_reorder, D.
        * auto.
        * apply card_in_rem in D. omega.
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.
  Proof.
    intros D E F.
    decide (card A = card B) as [G|G].
    + exfalso. apply F. apply (card_equi D); auto.
    + apply card_le in D. omega.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.
  Proof.
    intros D.
    decide (card A = card B) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. omega.
  Qed.

End Cardinality.

Instance card_equi_proper (X: eqType) : 
  Proper (@equi X ==> eq) (@card X).
Proof. 
  hnf. apply card_eq.
Qed.

(** *** Duplicate-free lists *)

Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_cons x A :
    dupfree (x::A) <-> ~ x el A /\ dupfree A.
  Proof. 
    split; intros D.
    - inv D; auto.
    - apply dupfreeC; tauto.
  Qed.

  Lemma dupfree_app A B :
    disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).
  Proof.
    intros D E F. induction E as [|x A E' E]; cbn.
    - exact F.
    - apply disjoint_cons in D as [D D'].
      constructor; [|exact (IHE D')].
      intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).
  Proof.
    intros D E. induction E as [|x A E' E]; cbn.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p A :
    dupfree A -> dupfree (filter p A).
  Proof.
    intros D. induction D as [|x A C D]; cbn.
    - left.
    - destruct (p x) eqn:E; [|exact IHD].
      right; [|exact IHD].
      rewrite in_filter_iff, E. intuition.
  Qed.

End Dupfree.

Section Undup.
  Variable X : eqType.
  Implicit Types A B : list X.

  Lemma dupfree_dec A :
    dec (dupfree A).
  Proof.
    induction A as [|x A].
    - left. left.
    - decide (x el A) as [E|E].
      + right. intros F. inv F; tauto.
      + destruct (IHA) as [F|F].
        * unfold dec. auto using dupfree.
        * right. intros G. inv G; tauto.
  Qed.

  Lemma dupfree_card A :
    dupfree A -> card A = |A|.
  Proof.
    induction 1 as [|x A D _ IH]; cbn.
    - reflexivity.
    - decide (x el A) as [G|].
      + exfalso; auto.
      + omega.
  Qed.

  Fixpoint undup (A : list X) : list X :=
    match A with
      | nil => nil
      | x::A' => if Dec (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; cbn.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; cbn.
    - left.
    - decide (x el A) as [E|E]; auto.
      right; auto. now rewrite undup_id_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_id A :
    dupfree A -> undup A = A.
  Proof.
    intros E. induction E as [|x A E F]; cbn.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_id, dupfree_undup. Qed.

End Undup.

(** *** Power lists *)

Section Power.
  Variable X : Type.

  Fixpoint power (U: list X ) : list (list X) :=
    match U with
    | nil => [nil]
    | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.
  Proof.
    revert A; induction U as [|x U]; cbn; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      auto.
  Qed.

  Lemma power_nil U :
    nil el power U.
  Proof.
    induction U; cbn; auto.
  Qed.

End Power.

Section PowerRep.
  Variable X : eqType.
  Implicit Types A U : list X.

  Definition rep (A U : list X) : list X :=
    filter (fun x => Dec (x el A)) U.

  Lemma rep_cons A x U :
    x el A -> rep A (x::U) = x :: rep A U.
  Proof.
    intros H. apply filter_fst. auto.
  Qed.

  Lemma rep_cons' A x U :
    ~ x el A -> rep A (x::U) = rep A U.
  Proof.
    intros H. apply filter_fst'. auto.
  Qed.

  Lemma rep_cons_eq x A U :
    ~ x el U -> rep (x::A) U = rep A U.
  Proof.
    intros D. apply filter_pq_eq. intros y E.
    apply Dec_reflect_eq. split.
    - intros [<-|F]; tauto.
    - auto.
  Qed.

  Lemma rep_power A U :
    rep A U el power U.
  Proof.
    revert A; induction U as [|x U]; intros A.
    - cbn; auto.
    - decide (x el A) as [H|H].
      + rewrite (rep_cons _ H). cbn. auto using in_map.
      + rewrite (rep_cons' _ H). cbn. auto.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.
  Proof.
    intros x. unfold rep. rewrite in_filter_iff, Dec_reflect.
    intuition.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof.
    intros D E. apply in_filter_iff; auto.
  Qed.

  Lemma rep_equi A U :
    A <<= U -> rep A U === A.
  Proof.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.
  Proof.
    intros D. apply filter_pq_mono.
    intros E; rewrite !Dec_reflect; auto.
  Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. auto.
  Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. firstorder.
  Qed.

  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.
  Proof.
    intros D E F. transitivity (rep A U). 
    - symmetry. apply rep_equi, D.
    - rewrite F. apply rep_equi, E.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.
  Proof. 
    unfold rep at 1 3. apply filter_pq_eq.
    intros x D. apply Dec_reflect_eq. split.
    + apply rep_incl.
    + intros E. apply in_filter_iff. auto.
  Qed.
    
  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).
  Proof.
    intros D. induction D as [|x U E D]; cbn.
    - constructor. now auto. constructor.
    - apply dupfree_app.
      + intros [A [F G]]. apply in_map_iff in G as [A' [G G']].
        subst A. apply E. apply (power_incl F). auto.
      + exact IHD.
      + apply dupfree_map; congruence.
  Qed.

  Lemma dupfree_in_power U A :
    A el power U -> dupfree U -> dupfree A.
  Proof.
    intros E D. revert A E.
    induction D as [|x U D D']; cbn; intros A E.
    - destruct E as [[]|[]]. constructor.
    - apply in_app_iff in E as [E|E].
      + auto.
      + apply in_map_iff in E as [A' [E E']]. subst A.
        constructor.
        * intros F; apply D. apply (power_incl E'), F.
        * auto.
  Qed.

  Lemma rep_dupfree A U :
    dupfree U -> A el power U -> rep A U = A.
  Proof.
    intros D; revert A. 
    induction D as [|x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - cbn in G. apply in_app_iff in G as [G|G]. 
      + rewrite rep_cons'. now auto.
        contradict E. apply (power_incl G), E.
      + apply in_map_iff in G as [A' [<- H]].
        specialize (IHF _ H).
        rewrite rep_cons. Focus 2. now auto.
        rewrite rep_cons_eq. now rewrite IHF. exact E.
   Qed.

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.
  Proof.
    intros D E F G. 
    rewrite <- (rep_dupfree D E). rewrite <- (rep_dupfree D F).
    apply rep_eq, G.
  Qed.

End PowerRep.


Definition elAt := nth_error.
Notation "A '.[' i  ']'" := (elAt A i) (no associativity, at level 50).

Section Fix_X.

  Variable X : Type.
  Context {Eq_dec : eq_dec X}.
  
  Fixpoint pos (s : X) (A : list X) :=
    match A with
    | nil => None
    | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end
    end.
  
  Lemma el_pos s A : s el A -> exists m, pos s A = Some m.
  Proof.
    revert s; induction A; simpl; intros s H.
    - contradiction.
    - decide (s = a) as [D | D]; eauto; 
        destruct H; try congruence.
      destruct (IHA s H) as [n Hn]; eexists; now rewrite Hn.
  Qed.
  
  Lemma pos_elAt s A i : pos s A = Some i -> A .[i] = Some s.
  Proof.
    revert i s. induction A; intros i s.
    - destruct i; inversion 1.
    - simpl. decide (s = a).
      + inversion 1; subst; reflexivity.
      + destruct i; destruct (pos s A) eqn:B; inversion 1; subst; eauto. 
  Qed.
  
  Lemma elAt_app (A : list X) i B s : A .[i] = Some s -> (A ++ B).[i] = Some s.
  Proof.
    revert s B i. induction A; intros s B i H; destruct i; simpl; intuition; inv H.
  Qed.
  
  Lemma elAt_el  A (s : X) m : A .[ m ] = Some s -> s el A.
  Proof.
    revert A. induction m; intros []; inversion 1; eauto.
  Qed.
  
  Lemma el_elAt (s : X) A : s el A -> exists m, A .[ m ] = Some s.
  Proof.
    intros H; destruct (el_pos H);  eexists; eauto using pos_elAt.
  Qed.

  Lemma dupfree_elAt (A : list X) n m s : dupfree A -> A.[n] = Some s -> A.[m] = Some s -> n = m.
  Proof with try tauto.
    intros H; revert n m; induction A; simpl; intros n m H1 H2.
    - destruct n; inv H1.
    - destruct n, m; inv H...
      + inv H1. simpl in H2. eapply elAt_el in H2...
      + inv H2. simpl in H1. eapply elAt_el in H1... 
      + inv H1. inv H2. rewrite IHA with n m... 
  Qed.

  Lemma nth_error_none A n l : nth_error l n = @None A -> length l <= n.
  Proof. revert n;
           induction l; intros n.
         - simpl; omega.
         - simpl. intros. destruct n. inv H. inv H. assert (| l | <= n). eauto. omega.
  Qed.

  Lemma pos_None (x : X) l l' : pos x l = None-> pos x l' = None -> pos x (l ++ l') = None.
  Proof.
    revert x l'; induction l; simpl; intros; eauto.
    have (x = a).
    destruct (pos x l) eqn:E; try congruence.
    rewrite IHl; eauto.
  Qed.

  Lemma pos_first_S (x : X)  l l' i  : pos x l = Some i -> pos x (l ++ l') = Some i.
  Proof.
    revert x i; induction l; intros; simpl in *.
    - inv H.
    - decide (x = a); eauto.
      destruct (pos x l) eqn:E.
      + eapply IHl in E. now rewrite E.
      + inv H.
  Qed.

  Lemma pos_second_S x l l' i : pos x l = None ->
                                pos x l' = Some i ->
                                pos x (l ++ l') = Some ( i + |l| ).
  Proof.
    revert i l'; induction l; simpl; intros.
    - rewrite plus_comm. eauto.
    - destruct _; subst; try congruence.
      destruct (pos x l) eqn:EE. congruence.
      erewrite IHl; eauto.
  Qed.

  Lemma pos_length (e : X) n E : pos e E = Some n -> n < |E|.
  Proof.
    revert e n; induction E; simpl; intros.
    - inv H.
    - decide (e = a).
      + inv H. simpl. omega.
      + destruct (pos e E) eqn:EE.
        * inv H. assert (n1 < |E|) by eauto.  omega.
        * inv H.
  Qed.

  Fixpoint replace (xs : list X) (y y' : X) :=
    match xs with
    | nil => nil
    | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y'
    end.

  Lemma replace_same xs x : replace xs x x = xs.
  Proof.
    revert x; induction xs; intros; simpl; [ | destruct _; subst ]; congruence.
  Qed.

  Lemma replace_diff xs x y : x <> y -> ~ x el replace xs x y.
  Proof.
    revert x y; induction xs; intros; simpl; try destruct _; firstorder. 
  Qed.

  Lemma replace_pos xs x y y' : x <> y -> x <> y' -> pos x xs = pos x (replace xs y y').
  Proof.
    induction xs; intros; simpl.
    - reflexivity.
    - repeat destruct Dec; try congruence; try omega; subst. 
      + rewrite IHxs; eauto. + rewrite IHxs; eauto.
  Qed.

End Fix_X.

Arguments replace {_} {_} _ _ _.



(* Fixpoint  getPosition {E: eqType} (A: list E) x := match A with *)
(*                                                    | nil => 0 *)
(*                                                    | cons x' A' => if Dec (x=x') then 0 else 1 + getPosition A' x end. *)

(* Lemma getPosition_correct {E: eqType} (x:E) A: if Dec (x el A) then forall z, (nth (getPosition A x) A z) = x else getPosition A x = |A |. *)
(* Proof. *)
(*   induction A;cbn. *)
(*   -dec;tauto. *)
(*   -dec;intuition; congruence. *)
(* Qed. *)
