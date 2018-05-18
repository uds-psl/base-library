(* Library for injections, bijections, and retracts  *)
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
 *
 * The retracts should also be "tight", which means that the retract function only reverts values in
 * the image of [f]. Foramlly this means that whenever [g y = Some x], then also [y = f x]
 *
 * Altogether, we have that [forall x y, g y = Some x <-> y = f x].
 *)


Section Retract.

  Variable X Y : Type.

  Definition retract (f : X -> Y) (g : Y -> option X) := forall x y, g y = Some x <-> y = f x.

  Class Retract :=
    {
      Retr_f : X -> Y;
      Retr_g : Y -> option X;
      Retr_retr : retract Retr_f Retr_g;
    }.

  Hypothesis I : Retract.

End Retract.

Arguments Retr_f { _ _ _ }.
Arguments Retr_g { _ _ _ }.

Section Retract_Properties.

  Variable X Y : Type.

  Hypothesis I : Retract X Y.

  Definition retract_g_adjoint : forall x, Retr_g (Retr_f x) = Some x.
  Proof. intros. pose proof @Retr_retr _ _ I. hnf in H. now rewrite H. Qed.

  Definition retract_g_inv : forall x y, Retr_g y = Some x -> y = Retr_f x.
  Proof. intros. now apply Retr_retr. Qed.

  Lemma retract_g_surjective : forall x, { y | Retr_g y = Some x }.
  Proof. intros x. pose proof retract_g_adjoint x. cbn in H. eauto. Defined.

  Lemma tretract_f_injective : forall x1 x2, Retr_f x1 = Retr_f x2 -> x1 = x2.
  Proof.
    intros x1 x2 H.
    enough (Some x1 = Some x2) by congruence.
    erewrite <- !retract_g_adjoint.
    now rewrite H.
  Qed.

End Retract_Properties.


(* This tactic replaces all occurrences of [g (f x)] with [Some x] for retracts. *)
Ltac retract_adjoint :=
  match goal with
  | [ H : context [ Retr_g (Retr_f _) ] |- _ ] => rewrite retract_g_adjoint in H
  | [   |- context [ Retr_g (Retr_f _) ]     ] => rewrite retract_g_adjoint
  end.



(*
 * We can compose Compose retracts, as shown in the following commuting diagram
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

  (* No instance (outside of this section), for obvious reasons... *)
  Local Instance ComposeTRetract (retr1 : Retract A B) (retr2 : Retract B C) : Retract A C :=
    {|
      Retr_f := retr_comp_f Retr_f Retr_f;
      Retr_g := retr_comp_g Retr_g Retr_g;
    |}.
  Proof.
    abstract now
      unfold retr_comp_f, retr_comp_g; intros a c; split;
      [intros H; destruct (Retr_g c) as [ | ] eqn:E;
       [ apply retract_g_inv in E as ->; now apply retract_g_inv in H as ->
       | congruence
       ]
      | intros ->; now do 2 retract_adjoint
      ].
  Defined.

End ComposeRetracts.


Section Inversion_Retract.
  Variable A B : Type.

  Global Instance Inversion_Retract (inv : Inversion A B) : Retract A B :=
    {|
      Retr_f a := Inv_f a;
      Retr_g b := Some (Inv_g b);
    |}.
  Proof.
    abstract now
      hnf; intros a b; split;
      [ inversion 1; now inverse
      | intros ->; now inverse
      ].
  Defined.

End Inversion_Retract.



(** We define some other useful retracts, that do not correspond to inversions *)
Section Usefull_Retracts.

  Variable (A B C D : Type).


  (** We can introduce an additional [Some] and use the identity as the retract function *)
  Global Instance Retract_option `{retr: Retract A B} : Retract A (option B) :=
    {|
      Retr_f a := Some (Retr_f a);
      Retr_g ob := match ob with
                    | Some b => Retr_g b
                    | None => None
                    end;
    |}.
  Proof.
    abstract now
      split;
      [ intros H; destruct y as [b|];
        [ now apply retract_g_inv in H as ->
        | inv H
        ]
      | intros ->; now retract_adjoint
      ].
  Defined.

  (** We can introduce an additional [inl] *)

  Definition retract_inl_f (f : A -> B) : A -> (B + C) := fun a => inl (f a).
  Definition retract_inl_g (g : B -> option A) : B+C -> option A :=
    fun x => match x with
          | inl b => g b
          | inr c => None
          end.

  Global Instance TRetract_inl (retrAB : Retract A B) : Retract A (B + C) :=
    {|
      Retr_f := retract_inl_f Retr_f;
      Retr_g := retract_inl_g Retr_g;
    |}.
  Proof.
    abstract now
      unfold retract_inl_f, retract_inl_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ now intros -> % retract_g_inv | congruence ]
      | intros ->; now retract_adjoint
      ].
  Defined.


  (** The same for [inr] *)

  Definition retract_inr_f (f : A -> B) : A -> (C + B) := fun a => inr (f a).
  Definition retract_inr_g (g : B -> option A) : C+B -> option A :=
    fun x => match x with
          | inr b => g b
          | inl c => None
          end.

  Global Instance Retract_inr (retrAB : Retract A B) : Retract A (C + B) :=
    {|
      Retr_f := retract_inr_f Retr_f;
      Retr_g := retract_inr_g Retr_g;
    |}.
  Proof.
    abstract now
      unfold retract_inr_f, retract_inr_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ congruence | now intros -> % retract_g_inv ]
      | intros ->; now retract_adjoint
      ].
  Defined.



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
    Proof.
      abstract now
        unfold retract_sum_f, retract_sum_g; intros x y; split;
        [ intros H; destruct y as [c|d];
          [ destruct (Retr_g c) eqn:E1; inv H; f_equal; now apply retract_g_inv
          | destruct (Retr_g d) eqn:E1; inv H; f_equal; now apply retract_g_inv
          ]
        | intros ->; destruct x as [a|b]; now retract_adjoint
        ].
    Defined.

  End Retract_sum.

End Usefull_Retracts.






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