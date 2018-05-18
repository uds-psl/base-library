(* Library for injections, bijections, retracts and tight retracts *)
Require Import Shared.Base.


(** * Bijections / Inversions *)

Section Inversion.
  Variable X Y : Type.

  (*
   *      f
   *   ------>
   * X         Y
   *   <------
   *      g
   *)

  Definition left_inverse  (f : X -> Y) (g : Y -> X) := forall x : X, g (f x) = x.
  Definition right_inverse (f : X -> Y) (g : Y -> X) := forall y : Y, f (g y) = y.

  (* Class that holds the existence of an inversion between [X] and [Y] *)
  Class Inversion :=
    {
      Inv_f : X -> Y;
      Inv_g : Y -> X;
      Inv_inv_left : left_inverse Inv_f Inv_g;
      Inv_inv_right : right_inverse Inv_f Inv_g;
    }.
End Inversion.

Arguments Inv_f { _ _ _ }.
Arguments Inv_g { _ _ _ }.


(* This tactic replaces [f (g x)] and [g (f x)] with [x] for inversions. *)
Ltac inverse :=
  match goal with
  | [ H : context [ Inv_g (Inv_f _) ] |- _] =>
    rewrite Inv_inv_left in H
  | [ H : context [ Inv_f (Inv_g _) ] |- _] =>
    rewrite Inv_inv_right in H
  | [ |- context [ Inv_g (Inv_f _) ] ] =>
    rewrite Inv_inv_left
  | [ |- context [ Inv_f (Inv_g _) ] ] =>
    rewrite Inv_inv_right
  end.


Section Inverse_Test.
  Variable X Y : Type.
  Variable I : Inversion X Y.

  Goal forall x, Inv_f (Inv_g x) = x.
  Proof.
    intros x. inverse. reflexivity.
  Qed.

End Inverse_Test.


Section Useful_Inversions.

  Variable A B C D : Type.

  (* The existence of inversions is a equivalence relation. *)
  Section Inversion_Equivalence.

    Global Instance Inversion_Id : Inversion A A :=
      {|
        Inv_f := id;
        Inv_g := id;
      |}.
    Proof. all: abstract firstorder. Defined.

    (* This must not be an Instance, because this would create a loop within [typeclasses eauto] *)
    Local Instance Inversion_Comp (I1 : Inversion A B) (I2 : Inversion B C) : Inversion A C :=
      {|
        Inv_f a := Inv_f (Inv_f a);
        Inv_g c := Inv_g (Inv_g c);
      |}.
    Proof. all: abstract now hnf; firstorder; do 2 inverse. Defined.

    Local Instance Inversion_Symmetric (I : Inversion A B) : Inversion B A :=
      {|
        Inv_f := fun a => Inv_g a;
        Inv_g := fun b => Inv_f b;
      |}.
    Proof. all: abstract now hnf; firstorder; inverse. Defined.


  End Inversion_Equivalence.

  Section Inversion_sum.

    (*
     * A <-> C         B <-> D
     * A + B   <---->  C + D
     *)

    Global Instance Inversion_sum (I1 : Inversion A C) (I2 : Inversion B D) : Inversion (A+B) (C+D) :=
      {|
        Inv_f x := match x with
                   | inl a => inl (Inv_f a)
                   | inr c => inr (Inv_f c)
                   end;
        Inv_g y := match y with
                   | inl c => inl (Inv_g c)
                   | inr d => inr (Inv_g d)
                   end;
      |}.
    Proof. all: abstract now hnf; intros [x|y]; f_equal; inverse. Defined.

  End Inversion_sum.

  Section Inversion_sum_swap.

    (*
     * A + B <-> B + A
     *)

    (* No Instance because it could be applyed many times *)
    Local Instance Inversion_sum_swap : Inversion (A + B) (B + A) :=
      {|
        Inv_f x := match x with
                   | inl a => inr a
                   | inr b => inl b
                   end;
        Inv_g y := match y with
                   | inl a => inr a
                   | inr b => inl b
                   end;
      |}.
    Proof. all: abstract now hnf; intros [x|y]; f_equal; inverse. Defined.

  End Inversion_sum_swap.
 
  Section Inversion_sum_Empty_set.

    Global Instance Inversion_sum_Empty : Inversion (A + Empty_set) A :=
      {|
        Inv_f x := match x : A + Empty_set with
                   | inl a => a
                   | inr e => Empty_set_rect _ e
                   end;
        Inv_g a := inl a;
      |}.
    Proof. abstract now hnf; intros [ x | [] ]. abstract now hnf; auto. Defined.

  End Inversion_sum_Empty_set.

  Section Inversion_Option_Unit.

    Global Instance Inversion_Option_Unit : Inversion (option A) (A + unit) :=
      {|
        Inv_f x := match x with
                   | Some y => inl y
                   | None => inr tt
                   end;
        Inv_g y := match y with
                   | inl a => Some a
                   | inr _ => None
                   end;
      |}.
    Proof. abstract now hnf; intros [ a | ]. abstract now hnf; intros [ a | [] ]. Defined.

  End Inversion_Option_Unit.


  Section Inversion_Involution.
    Variable f : A -> A.
    Hypothesis f_inv : forall a, f (f a) = a.

    Local Instance Inversion_Involution : Inversion A A :=
      {|
        Inv_f := f;
        Inv_g := f;
      |}.
    Proof. all: abstract now auto. Defined.

  End Inversion_Involution.

End Useful_Inversions.






(*
 * A retract between types [A] and [B] is a tuple of two functions,
 * [f : A -> B] (called the injection function) and [g : B -> option A] (called the retract function),
 * such that the following triangle shaped diagram commutes:
 *
 *          f
 *      A -----> B
 *      |      /
 * Some |     / g
 *      |    /
 *     \|/ |/_
 *    option A
 *
 * That informally means, that the injective function [f] can be reverted by the retract function [g].
 * Foramlly, for all values [x:A] and [y = f x], then [g y = Some x].  (Or: [forall x, g (f x) = Some x].)
 *)


Section Retract.

  Variable X Y : Type.

  Definition retract (f : X -> Y) (g : Y -> option X) := forall x, g (f x) = Some x.

  Class Retract :=
    {
      Retr_f : X -> Y;
      Retr_g : Y -> option X;
      Retr_adj : retract Retr_f Retr_g;
    }.

  Hypothesis I : Retract.

  Definition retract_g_adjoint : forall x, Retr_g (Retr_f x) = Some x := Retr_adj.

  Lemma retract_g_surjective : forall x, { y | Retr_g y = Some x }.
  Proof. intros x. pose proof Retr_adj x. eauto. Defined.

  Lemma retract_f_injective : forall x1 x2, Retr_f x1 = Retr_f x2 -> x1 = x2.
  Proof.
    intros x1 x2 H. enough (Some x1 = Some x2) as HE by now inv HE.
    erewrite <- Retr_adj; eauto. rewrite H. apply Retr_adj.
  Qed.

End Retract.

Arguments Retr_f { _ _ _ }.
Arguments Retr_g { _ _ _ }.

(*
 * An tight retract has the additional property, that the retract function only reverts values in the image of [f].
 * Foramlly this means that whenever [g y = Some x], then also [y = f x]
 * All properties of retracts hold automatically for tight retracts, since every tight retract "is" a retract.
 *)
Section TightRetract.

  Variable X Y : Type.

  Definition tight_retract (f : X -> Y) (g : Y -> option X) := forall x y, g y = Some x <-> y = f x.

  Class TRetract :=
    {
      TRetr_f : X -> Y;
      TRetr_g : Y -> option X;
      TRetr_inv : tight_retract TRetr_f TRetr_g;
    }.

  Hypothesis I : TRetract.

  Global Instance TRetract_Retract : Retract X Y :=
    {|
      Retr_f := TRetr_f;
      Retr_g := TRetr_g;
    |}.
  Proof. abstract now intros x; apply TRetr_inv. Defined.

  Definition TRetr_inv' : forall x y, TRetr_g y = Some x -> y = TRetr_f x := ltac:(apply I).

End TightRetract.

Arguments TRetr_f { _ _ _ }.
Arguments TRetr_g { _ _ _ }.

Coercion TRetract_Retract : TRetract >-> Retract.


(* The above instance [TRetract_Retract] that is also used as implcit coercion makes sure that we can
 * use tight retracts in place of normal retracts. *)

Section TightRetract_InheritedProperties.

  Variable X Y : Type.

  Hypothesis I : TRetract X Y.

  Definition tretract_g_adjoint : forall x, TRetr_g (TRetr_f x) = Some x := ltac:(intros x; now apply TRetr_inv).

  (* Here we only apply lemmas of normal retracts!  The coercion is not used, but the instance [TRetract_Retract] *)
  Lemma tretract_g_surjective : forall x, { y | TRetr_g y = Some x }.
  Proof. intros x. pose proof Retr_adj x. cbn in H. eauto. Defined.

  Lemma tretract_f_injective : forall x1 x2, TRetr_f x1 = TRetr_f x2 -> x1 = x2.
  Proof. intros x1 x2 H. eapply retract_f_injective. cbn. eauto. Qed.

End TightRetract_InheritedProperties.



(* This tactic replaces all occurrences of [g (f x)] with [Some x] for (tight) retracts. *)
Ltac retract_adjoint :=
  match goal with
  | [ H : context [ Retr_g (Retr_f _) ] |- _ ] => rewrite retract_g_adjoint in H
  | [   |- context [ Retr_g (Retr_f _) ]     ] => rewrite retract_g_adjoint
  | [ H : context [ TRetr_g (TRetr_f _) ] |- _ ] => rewrite tretract_g_adjoint in H
  | [   |- context [ TRetr_g (TRetr_f _) ]     ] => rewrite tretract_g_adjoint
  end.




(*
 * We can compose Compose (tight) retracts, as shown in the following commuting diagram
 *
 *            f1        f2
 *      A --------> B --------> C
 *      |         / |         /
 *      |        /  |Some    /
 *      |       /   |       /
 *      |      /    |      /
 * Some |     / g1  |     / g2
 *      |    /      |    /
 *     \|/ |/_     \|/ |/_
 *    option A <--- option B
 *            map g1
 *
 *
 * Where [map g1] is the function that takes an option [x : option B] and applys [Some] and [g1] if it is [Some],
 * and else returns [None].
 *
 * Now [f2 ∘ f1] and [map g1 ∘ g2] gives a retract between [A] and [C].
 *)

Section ComposeRetracts.
  Variable A B C : Type.

  Definition retr_comp_f (f1 : A -> B) (f2 : B -> C) : A -> C := fun a => f2 (f1 a).
  Definition retr_comp_g (g1 : B -> option A) (g2 : C -> option B) :=
    fun c => match g2 c with
          | Some b => g1 b
          | None => None
          end.

  (* No instance, for obvious reasons... *)
  Local Instance ComposeRetract (retr1 : Retract A B) (retr2 : Retract B C) : Retract A C :=
    {|
      Retr_f := retr_comp_f Retr_f Retr_f;
      Retr_g := retr_comp_g Retr_g Retr_g;
    |}.
  Proof. abstract now unfold retr_comp_f, retr_comp_g; intros a; do 2 retract_adjoint. Defined.


  Local Instance ComposeTRetract (retr1 : TRetract A B) (retr2 : TRetract B C) : TRetract A C :=
    {|
      TRetr_f := retr_comp_f TRetr_f TRetr_f;
      TRetr_g := retr_comp_g TRetr_g TRetr_g;
    |}.
  Proof.
    abstract now
      unfold retr_comp_f, retr_comp_g; intros a c; split;
      [intros H; destruct (TRetr_g c) as [ | ] eqn:E;
       [ apply TRetr_inv in E as ->; now apply TRetr_inv in H as ->
       | congruence
       ]
      | intros ->; now do 2 retract_adjoint
      ].
    (*
    hnf. intros a c. split.
    - intros H. destruct (TRetr_g c) as [b | ] eqn:E.
      + apply TRetr_inv in E as ->. apply TRetr_inv in H as ->. auto.
      + congruence.
    - intros ->. now do 2 rewrite tretract_g_adjoint.
     *)
  Defined.

End ComposeRetracts.


(* We can build a tight retract from an inversion, by applying [Some] in [g]. *)
(* TODO/Note: To build a (normal) retract, we only need an injective function. *)

Section Inversion_TRetract.
  Variable A B : Type.

  Global Instance Inversion_TRetract (inv : Inversion A B) : TRetract A B :=
    {|
      TRetr_f a := Inv_f a;
      TRetr_g b := Some (Inv_g b);
    |}.
  Proof.
    abstract now
      hnf; intros a b; split;
      [ inversion 1; now inverse
      | intros ->; now inverse
      ].
    (*
    hnf. intros a b. split.
    - inversion 1. now inverse.
    - intros ->. now inverse.
     *)
  Defined.


  (* Note:  We don't need to show that we can build a retract from an inversion,
   * since we can build a retract from a tight retract from an inversion. *)

End Inversion_TRetract.



(** We define some other useful retracts, that do not correspond to inversions *)


Section Usefull_Retracts.

  Variable (A B C D : Type).


  (** We can introduce an additional [Some] and use the identity as the retract function *)
  Global Instance TRetract_option `{retr: TRetract A B} : TRetract A (option B) :=
    {|
      TRetr_f a := Some (TRetr_f a);
      TRetr_g ob := match ob with
                    | Some b => TRetr_g b
                    | None => None
                    end;
    |}.
  Proof.
    abstract now
      split;
      [ intros H; destruct y as [b|];
        [ now apply TRetr_inv in H as ->
        | inv H
        ]
      | intros ->; now retract_adjoint
      ].
  (*
    split.
    - intros H. destruct y as [b|]; auto. now apply TRetr_inv' in H as ->. inv H.
    - intros ->. now retract_adjoint.
     *)
  Defined.

  Global Instance Retract_option `{retr: Retract A B} : Retract A (option B) :=
    {|
      Retr_f a := Some (Retr_f a);
      Retr_g ob := match ob with
                    | Some b => Retr_g b
                    | None => None
                    end;
    |}.
  Proof. abstract now intros a; retract_adjoint. Defined.

  (** We can introduce an additional [inl] *)

  Definition retract_inl_f (f : A -> B) : A -> (B + C) := fun a => inl (f a).
  Definition retract_inl_g (g : B -> option A) : B+C -> option A :=
    fun x => match x with
          | inl b => g b
          | inr c => None
          end.

  Global Instance TRetract_inl (retrAB : TRetract A B) : TRetract A (B + C) :=
    {|
      TRetr_f := retract_inl_f TRetr_f;
      TRetr_g := retract_inl_g TRetr_g;
    |}.
  Proof.
    abstract now
      unfold retract_inl_f, retract_inl_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ now intros -> % TRetr_inv | congruence ]
      | intros ->; now retract_adjoint
      ].
  Defined.

  Global Instance Retract_inl (retrAB : Retract A B) : Retract A (B + C) :=
    {|
      Retr_f := retract_inl_f Retr_f;
      Retr_g := retract_inl_g Retr_g;
    |}.
  Proof. abstract now intros a; cbn; now retract_adjoint. Defined.


  (** The same for [inr] *)

  Definition retract_inr_f (f : A -> B) : A -> (C + B) := fun a => inr (f a).
  Definition retract_inr_g (g : B -> option A) : C+B -> option A :=
    fun x => match x with
          | inr b => g b
          | inl c => None
          end.

  Global Instance TRetract_inr (retrAB : TRetract A B) : TRetract A (C + B) :=
    {|
      TRetr_f := retract_inr_f TRetr_f;
      TRetr_g := retract_inr_g TRetr_g;
    |}.
  Proof.
    abstract now
      unfold retract_inr_f, retract_inr_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ congruence | now intros -> % TRetr_inv ]
      | intros ->; now retract_adjoint
      ].
  Defined.

  Global Instance Retract_inr (retrAB : Retract A B) : Retract A (C + B) :=
    {|
      Retr_f := retract_inr_f Retr_f;
      Retr_g := retract_inr_g Retr_g;
    |}.
  Proof. abstract now intros a; cbn; now retract_adjoint. Defined.


  (** We can map retracts over sums, similiary as we have done with inversions *)

  Section Retract_sum.

    Definition retract_sum_f (f1: A -> C) (f2: B -> D) : A+B -> C+D :=
      fun x => match x with
            | inl a => inl (f1 a)
            | inr b => inr (f2 b)
            end.

    Definition retract_sum_g (g1: C -> option A) (g2: D -> option B) : C+D -> option (A+B) :=
      fun y => match y with
            | inl c => match g1 c with
                      | Some a => Some (inl a)
                      | None => None
                      end
            | inr d => match g2 d with
                      | Some b => Some (inr b)
                      | None => None
                      end
            end.

    Local Instance Retract_sum (retr1 : Retract A C) (retr2 : Retract B D) : Retract (A+B) (C+D) :=
      {|
        Retr_f := retract_sum_f Retr_f Retr_f;
        Retr_g := retract_sum_g Retr_g Retr_g;
      |}.
    Proof. abstract now unfold retract_sum_f, retract_sum_g; hnf; intros [a | b]; retract_adjoint. Defined.


    (* Definition has to be copied again for tight retracts *)
    Local Instance TRetract_sum (retr1 : TRetract A C) (retr2 : TRetract B D) : TRetract (A+B) (C+D) :=
      {|
        TRetr_f := retract_sum_f TRetr_f TRetr_f;
        TRetr_g := retract_sum_g TRetr_g TRetr_g;
      |}.
    Proof.
      abstract now
        unfold retract_sum_f, retract_sum_g; intros x y; split;
        [ intros H; destruct y as [c|d];
          [ destruct (TRetr_g c) eqn:E1; inv H; f_equal; now apply TRetr_inv
          | destruct (TRetr_g d) eqn:E1; inv H; f_equal; now apply TRetr_inv
          ]
        | intros ->; destruct x as [a|b]; now retract_adjoint
        ].
      (*
      hnf. intros x y. split.
      - intros H. destruct y as [c|d]; cbn in *.
        + destruct (TRetr_g c) eqn:E1; inv H. f_equal. now apply TRetr_inv.
        + destruct (TRetr_g d) eqn:E1; inv H. f_equal. now apply TRetr_inv.
      - intros ->. destruct x as [a | b]; now retract_adjoint.
       *)
    Defined.

  End Retract_sum.

End Usefull_Retracts.



(* We can build a tight retract for every retract where the target type is decidable. *)

Section Retract_TRetract.
  Variable (X : Type) (Y : eqType).
  Hypothesis retr : Retract X Y.


  (* We can decide weather a value is in the image of the injection *)
  Global Instance retract_dec_in_image :
    forall y, dec (exists x, Retr_f x = y).
  Proof.
    intros y. destruct (Retr_g y) as [x | ] eqn:E.
    - decide (Retr_f x = y) as [<- | D].
      + left. eauto.
      + right. intros (x'&<-). enough (Some x' = Some x) by congruence.
        erewrite <- retract_g_adjoint; eauto.
    - right. intros (x&<-). rewrite retract_g_adjoint in E; eauto. congruence.
  Qed.

  Definition tretract_from_retr_g (g : Y -> option X) : Y -> option X :=
    fun y => if Dec (exists x, Retr_f x = y) then Retr_g y else None.

  Lemma retract_tretract : tight_retract Retr_f (tretract_from_retr_g Retr_g).
    unfold tretract_from_retr_g. hnf. intros x. split.
    - intros H. decide (exists x, Retr_f x = y) as [ (x'&<-) | D].
      + rewrite retract_g_adjoint in H; auto. congruence.
      + congruence.
    - intros ->. decide (exists x', Retr_f x' = Retr_f x) as [ (x'&Hx') | D].
      + rewrite retract_g_adjoint; auto.
      + contradict D. eauto.
  Qed.

  (* No instance here, or [typeclasses eauto] could cycle between [TRetract_Retract] and [Retract_TRetract] *)
  Local Instance Retract_TRetract : TRetract X Y.
  Proof. econstructor. apply retract_tretract. Defined.

End Retract_TRetract.


























(** * Injective functions *)

(* maybe deprecated *)

Section Injection.

  Variable X Y : Type.

  Definition injective (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.

  Class Injection :=
    {
      Inj_f : X -> Y;
      Inj_inj : injective Inj_f;
    }.

End Injection.

Arguments Inj_f { _ _ _ }.


(* Every inversion is also an injection *)
Section Inverse_Injective.
  Variable X Y : Type.

  Lemma left_inv_inj (f : X -> Y) (g : Y -> X) : left_inverse f g -> injective f.
  Proof.
    intros HInv. hnf in *. intros x1 x2 Heq.
    enough (g (f x1) = g (f x2)) as L by now rewrite !HInv in L.
    f_equal. assumption.
  Qed.

  Global Instance Inversion_Injection (inv : Inversion X Y) : Injection X Y :=
    {|
      Inj_f x := Inv_f x;
    |}.
  Proof. abstract now eapply left_inv_inj, Inv_inv_left. Defined.

End Inverse_Injective.

Coercion Inversion_Injection : Inversion >-> Injection.

Ltac inj_subst :=
  match goal with
  | [ H : Inj_f _ = Inj_f _ |- _] => apply Inj_inj in H
  end.


Section Useful_Injections.
  Variable A B C : Type.

  Global Instance Injection_Id : Injection A A :=
    {|
      Inj_f a := a;
    |}.
  Proof. abstract now hnf; auto. Defined.

  Global Instance Injection_Compose (inj1 : Injection A B) (inj2 : Injection B C) : Injection A C :=
    {|
      Inj_f a := Inj_f (Inj_f a);
    |}.
  Proof. abstract now hnf; intros; do 2 inj_subst. Defined.


End Useful_Injections.


(* (* TODO: Does this belong to here? *)
Section Map_Injective.
  Variable (sig tau : Type) (t : sig -> tau).
  Hypothesis t_injective : injective t.

  Global Instance map_injective :
    injective (map t).
  Proof.
    hnf. intros xs. induction xs; intros ys H; cbn in *.
    - erewrite map_eq_nil; eauto.
    - destruct ys; cbn in *; inv H. inj_subst. f_equal. auto.
  Qed.

End Map_Injective.
*)



(*
Global Instance retract_injective (A B : Type) (f : A -> B) (g : B -> option A) :
  retract f g -> injective f.
Proof.
  intros H. intros x1 x2 H2. eapply retract_f_injective; eauto.
Qed.
Hint Resolve retract_injective : inj.

Section Injection_Corollaries.
  Variable A B : Type.
  
  Instance injective_id : injective (@id A) := ltac:(now auto_inj).
  Instance injective_inl : injective (@inl A B) := ltac:(now auto_inj).
  Instance injective_inr : injective (@inr A B) := ltac:(now auto_inj).
  
End Injection_Corollaries.

Hint Resolve injective_id : inj.
Hint Resolve injective_inl : inj.
Hint Resolve injective_inr : inj.


(* TODO: Can any injection between decidable types be made a retract? *)
Section Dec_Retract.
nd Dec_Retract.
*)