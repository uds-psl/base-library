(* Inhabited types *)
Require Shared.Prelim.
Require Import Coq.Vectors.Vector Coq.Vectors.Fin.
Require Import FiniteTypes.FinTypes.

Class inhabitedC (X : Type) :=
  Inhabited
    {
      default : X
    }.


Structure inhabitedType :=
  InhabitedType
    {
      type :> Type;
      class : inhabitedC type
    }.

Arguments InhabitedType type {class}.
Existing Instance class | 0.

Canonical Structure inhabitedType_CS (X : Type) {class : inhabitedC X} : inhabitedType := @InhabitedType X class.

(*
Section Test.
  Variable x : inhabitedType.
  Set Printing All.
  Compute default : x.
  Unset Printing All.
End Test.
*)

Instance inhabited_unit : inhabitedC unit.
Proof. do 2 constructor. Defined.


Instance inhabited_inl (a b : Type) (inh_a : inhabitedC a) : inhabitedC (a + b).
Proof. constructor. left. apply default. Defined.

Instance inhabited_inr (a b : Type) (inh_b : inhabitedC b) : inhabitedC (a + b).
Proof. constructor. right. apply default. Defined.

Instance inhabited_option (a : Type) : inhabitedC (option a).
Proof. constructor. right. Defined.

Instance inhabited_bool : inhabitedC bool.
Proof. do 2 constructor. Defined.

Instance inhabited_list (a : Type) : inhabitedC (list a).
Proof. do 2 constructor. Defined.

Instance inhabited_vector (a : Type) (n : nat) (inh_a : inhabitedC a) : inhabitedC (Vector.t a n).
Proof. constructor. eapply VectorDef.const. apply default. Defined.

Instance inhabited_fin (n : nat) : inhabitedC (Fin.t (S n)).
Proof. do 2 constructor. Defined.

Instance inhabited_nat : inhabitedC nat.
Proof. do 2 constructor. Defined.


Instance inhabited_arrow (a b : Type) : inhabitedC b -> inhabitedC (a -> b).
Proof. intros. constructor. intros _. apply default. Defined.

Instance inhabited_arrow_empty (b : Type) : inhabitedC (Empty_set -> b).
Proof. intros. constructor. apply Empty_set_rect. Defined.


(*
Section Test2.
  Compute default : bool + bool.
  Compute default : bool + nat.

  Compute InhabitedType bool: inhabitedType.

  Goal default = true.
  Proof. cbn. reflexivity. Qed.
    

  Variable someFunction : inhabitedType -> inhabitedType.
  Compute someFunction (InhabitedType nat).

  (* Check, that inl and inr work *)
  Variable (A : inhabitedType) (B : Type).
  Compute someFunction A.

  Compute someFunction (InhabitedType (A + B)).
  Compute someFunction (InhabitedType (B + A)).

  Compute default : nat + bool.
End Test2.
*)


(*
Section Test3.
  Let F := InhabitedType bool.

  Require Import Shared.FiniteTypes.BasicFinTypes.

  Check inhabitedC (eqType_X (FinTypes.type (FinType (EqType bool)))).
  Eval simpl in inhabitedC (eqType_X (FinTypes.type (FinType (EqType bool)))).
  
  Program Definition G := InhabitedType (FinType (EqType bool)).
  Compute default : G.

  Compute default : F.

  Lemma finInhabited_inhabited : @inhabitedC F.
  Proof. auto. Qed.

  Compute default : F.
End Test3.
*)

Record inhabitedFinType :=
  InhabitedFinType
    {
      inhabitedFinType_type :> finType;
      inhabitedFinType_inhabited : inhabitedC inhabitedFinType_type;
    }.
Arguments InhabitedFinType X {class} : rename.

Canonical Structure inhabitedFinType_CS {X : finType} {class: inhabitedC X} : inhabitedFinType := InhabitedFinType X.

(*
Section Test4.

  Require Import Shared.FiniteTypes.BasicFinTypes.

  Variable someFunction : inhabitedFinType -> nat.

  Let F := InhabitedFinType (FinType (EqType bool)).

  Compute default : F.
  
  Compute someFunction F.

  Variable someFunction' : finType -> nat.

  Compute someFunction' F.
  
End Test4.
*)


Hint Extern 4 =>  (* Improves type class inference *)
match goal with
| [  F : inhabitedFinType |- inhabitedC (eqType_X (FinTypes.type ?FF))] =>
  apply inhabitedFinType_inhabited
end : typeclass_instances.

(*
Section Test5.

  Variable (F : inhabitedFinType).

  Check F : finType.

  Check inhabitedC (eqType_X (FinTypes.type (inhabitedFinType_type F))).
  Eval simpl in inhabitedC (eqType_X (FinTypes.type (inhabitedFinType_type F))).

  Check default : F.
  Compute default : F.
End Test5.
*)

Definition mk_inhabitedFin {X : finType} (x : X) := @InhabitedFinType X (@Inhabited X x).