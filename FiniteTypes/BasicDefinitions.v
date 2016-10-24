(* * Basic definitions of decidablility and Functions
- includes basic Lemmas about said functions 
 *)

Require Export Shared.Base.

(** * Definition of useful tactics *)

(** dec is used to destruct all decisions appearing in the goal or assumptions. *)
Ltac dec := repeat (destruct Dec).

(** This tactic completely solves listComplete goals for base types *)
Ltac listComplete := intros x; simpl; dec; destruct x; try congruence.
(** simplifies (decision x = x) *)
Ltac deq x := destruct (Dec (x=x)) as [[]  | isnotequal]; [> | contradict isnotequal; reflexivity] .

(** Conversion from Prop to bool*)

(* Coercion toBool (P: Prop) (D: dec P) := if Dec P then true else false. *)
(* Arguments toBool P {D}. *)

(** * Injectivity and surjectivity *)
Definition injective (X Y: Type) (f: X -> Y):= forall x y, f x = f y -> x = y.
Definition surjective (X Y : Type) (f : X -> Y) : Prop := forall y, exists x, f x = y.
Definition bijective (X Y: Type) (f: X -> Y): Prop := injective f /\ surjective f.


(* (** * Pure predicates  *)
 (* taken from the development of Herditarily finite sets by Prof. Smolka and Kathrin Stark. *)
 (* *) *)

(* Definition pure (X:Type) (p: X -> Prop) {D:forall x, dec (p x)} x := if Dec (p x) then True else False. *)
(* Arguments pure {X} p {D} x. *)

(* Lemma pure_equiv  (X:Type) (p: X -> Prop) {D:forall x, dec (p x)} x : p x <-> pure p x. *)
(* Proof. *)
(*   unfold pure. now dec. *)
(* Qed. *)

(* Lemma pure_impure  (P: Prop) (_: dec P) (norm: if Dec (P) then True else False) : P. *)
(* Proof. *)
(*   dec; tauto. *)
(* Qed. *)
(*   Ltac impurify H := pose proof (pure_impure H) as impureH; try (clear H; rename impureH into H). *)

(*   Lemma purify (X: Type) (p: X -> Prop) (D:forall x, dec (p x)) x (px: p x): pure p x. *)
(*   Proof. *)
(*    now  apply pure_equiv. *)
(*   Qed. *)

(* Arguments purify {X} {p} {D} {x} px. *)

(* Lemma pure_eq (X: Type) (p: X -> Prop) (D: forall x, dec (p x)) x (p1 p2: pure p x) : p1 = p2. *)
(* Proof. *)
(*   unfold pure in *.  dec. *)
(*   + now destruct p1, p2. *)
(*   + contradiction p1. *)
(* Qed. *)

(* (** * Proofs about equality *) *)
(* (* This proof was heavily inspired by the proof of this theorem in the Ssreflect library *) *)
(* Lemma Hedberg (X: eqType) (x y: X) (E E': x = y) : E = E'. *)
(* Proof. *)
(*   pose (f := fun y: X => fun E: x = y => match (Dec (x = y)) with                                    *)
(*                                    | left b => b *)
(*                                    | _ => E end). *)
(*   apply (@injectiveApply _ _(f y) E E'). Focus 2. *)
(*   - unfold f.  decide (x = y); tauto. *)
(*     pose (join := fun (y z : X) (e : x = y) => eq_trans (z := z) (eq_sym e)). *)
(*    apply  (@loop _ _ (f y)  (join x y (f x (eq_refl x)))). *)
(*     intros []. unfold f. now deq x. *)
(* Qed. *)
(* (* Idea taken from the Coq standard library *) *)
(* Theorem Streicher_K (X: eqType) (x:X) (P: x=x -> Prop): P (eq_refl x) ->  forall p, P p. *)
(* Proof. *)
(*   intros H p. now rewrite (Hedberg p (eq_refl x)). *)
(* Qed. *)

(* (** decision (x=x) will always yield the same result *) *)
(* Lemma DecRef (X: eqType) (x:X) : Dec (x = x) = left eq_refl. *)
(* Proof. *)
(*   dec. *)
(*   -  f_equal.  now apply (@Streicher_K _ _  (fun e => e = eq_refl x) ). *)
(*   - congruence. *)
(* Qed. *)

(* Hint Resolve DecRef. *)

(** dependent pairs   *)

(* Lemma sigT_proj1_fun (X: eqType) (f: X -> Type) (x x': X) (y: f x) (y': f x')  : *)
(*   existT f x y = existT f x' y' -> x = x'. *)
(* Proof. *)
(*  intro H. congruence. *)
(* Qed. *)

(* Import Logic.EqdepFacts. *)

(* Lemma sigT_proj2_fun (X: eqType) (f: X -> Type)  (E: forall x, eq_dec (f x)) (x: X) (y y': f x): *)
(*   existT f x y = existT f x y' -> y = y'. *)
(* Proof. *)
(*   intro H. *)
(*   rewrite <- (eq_sigT_snd H). *)
(*  now rewrite (Hedberg (eq_sigT_fst H) (eq_refl x)). *)
(* Qed. *)

(* Instance eq_dec_sigT (X: eqType) (f: X -> Type) (E: forall x, eq_dec (f x)) : eq_dec (sigT f). *)
(* Proof. *)
(*   intros p1 p2. *)
(*   destruct p1, p2. decide (x = x0). *)
(*   - subst x0. decide (f0 = f1). *)
(*     + left. congruence. *)
(*     + right. intro eq. apply n. now apply sigT_proj2_fun.       *)
(*   - right. intro H. apply n. apply (eq_funTrans (@projT1 _  f) H). *)
(* Qed. *)

(* (** subtypes *) *)
(* (* The idea of subtypes was taken from the HF_sets paper by Prof. Gert Smolka and Kathrin Stark *)
 (* They only defined one particular subtype, however. *) *)
(* Definition subtype {X:Type} (p: X -> Prop) {D: forall x, dec (p x)} := { x:X | pure p x}. *)
(* Arguments subtype {X} p {D}. *)

(* Lemma subtype_extensionality (X: Type) (p: X -> Prop)  {D: forall x, dec (p x)} (x x': subtype p) : proj1_sig x = proj1_sig x' <-> x = x'. *)
(* Proof. *)
(*   split. *)
(*   - intros H. destruct x, x'. cbn in H. subst x0. f_equal. apply pure_eq. *)
(*   - congruence.          *)
(* Qed. *)

(* Instance subType_eq_dec (X: eqType) (p: X -> Prop) (_: forall x, dec (p x)): eq_dec (subtype p). *)
(* Proof. *)
(*   intros y z. destruct y as [x p1], z as  [x' p2]. decide (x=x'). *)
(*   - left.  now apply subtype_extensionality. *)
(*   - right. intro H. apply n. apply (eq_funTrans (@proj1_sig _ (pure p)) H). *)
(* Qed.     *)

(* Lemma proj1_sig_fun (X: eqType) (p: X -> Prop) (x x': X) (p1: p x) (p2: p x'): exist p x p1 = exist p x' p2 -> x = x'. *)
(* Proof. *)
(*   intro E. change x with (proj1_sig (exist p x p1)). change x' with (proj1_sig (exist p x' p2)). *)
(*   now apply eq_funTrans. *)
(* Qed. *)




(* (** * Functions creating an eqType from a type or a value *) *)

(* Definition toeqType (T: Type) {e: eq_dec T} : eqType := EqType T.  *)
(* Arguments toeqType T {e}.  *)
(* Lemma toeqTypeCorrect (E: eqType) : E = toeqType E. *)
(* Proof. *)
(*   now destruct E. *)
(*  Qed. *)

(* (** * Definitions of corresponding eqTypes  *) *)
(* (* - Declaration as Canonical Structures to enable their inference later on *) *)

(* Canonical Structure  EqUnit := EqType unit. *)
(* Canonical Structure EqBool := EqType bool. *)
(* Canonical Structure EqNat := EqType nat. *)
(* Canonical Structure EqOption (T: eqType)  := EqType (option T). *)
(* Canonical Structure EqProd (T1 T2: eqType) := EqType (T1 * T2). *)
(* Canonical Structure EqEmpty_set := EqType Empty_set. *)
(* Canonical Structure EqFalse := EqType False. *)
(* Canonical Structure EqTrue := EqType True. *)
(* Canonical Structure EqSum (X Y: eqType) := EqType (X + Y). *)
(* Canonical Structure EqList (X: eqType) := EqType (list X). *)
(* Canonical Structure EqSigT (X: eqType) (f: X -> Type) {D: forall x, eq_dec (f x)} := EqType (sigT f). *)
(* Arguments EqSigT {X} f {D}. *)
(* Canonical Structure EqSubType (X: eqType) (p: X -> Prop) (D: forall x, dec (p x)) := EqType (subtype p). *)
(* Arguments EqSubType {X} p {D}. *)

(* (** * Useful notations for cross product and option eqTypes  *) *)
(* (* - The two different notations mean that arbitrary types are converted to eqTypes first but eqTypes are directly taken the way they are *) *)
(* Reserved Notation "T1 ** T2" (at level 69, no associativity). *)
(* Bind Scope EqTypeScope with eqType. *)
(* Notation "T1 ** T2" := (EqProd T1 T2): EqTypeScope. *)
(* Notation "T1 ** T2" := (EqProd (toeqType T1) (toeqType T2)). *)
(* Notation " ?? F" := (EqOption F) (at level 65). *)

(* (** * toeqType produces canonical instances *) *)
(* Set Printing Implicit. *)
(* Lemma toeqTypeCorrect_unit : toeqType unit = EqUnit. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_bool : toeqType bool = EqBool. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_nat : toeqType nat = EqNat. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_option (E: eqType) : toeqType (option E) = ?? E. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_prod (E E': eqType) : toeqType (E * E') = E ** E'. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_empty : toeqType Empty_set = EqEmpty_set. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_false : toeqType False = EqFalse. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_true : toeqType True = EqTrue. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqType_sum (E E': eqType): toeqType (E + E') = EqSum E E'. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_list (X: eqType) : toeqType (list X) = EqList X. *)
(* Proof.  *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqTypeCorrect_sigT (X: eqType) (f: X -> Type) {D: forall x, eq_dec (f x)} : toeqType {x:X & f x} = EqSigT f. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)


(* Lemma toeqTypeCorrect_sub (X: eqType) (p: X -> Prop) {D: forall x, dec (p x)} : toeqType (subtype p) = EqSubType p. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma toeqType_idempotent (X: Type) (_: eq_dec X) : toeqType (toeqType X) = toeqType X. *)
(* Proof. *)
(* reflexivity. *)
(* Qed. *)
(* Unset Printing Implicit. *)
(** * Definition of useful functions *)
(* - including some lemmas *)

(** Function that takes two lists and returns the list of all pairs of elements from the two lists *)
Fixpoint prodLists {X Y: Type} (A: list X) (B: list Y) {struct A} :=
  match A with
  | nil => nil
  | cons x A' => map (fun y => (x,y)) B ++ prodLists A' B end.

(** Crossing any list with the empty list always yields the empty list *)
Lemma prod_nil (X Y: Type) (A: list X) :
  prodLists A ([]: list Y) = [].
Proof.
  induction A.
  - reflexivity.
  - cbn. assumption.
Qed.

(** This function takes a (A: list X) and yields a list (option X) which for every x in A contains Some x. The resultung list also contains None. The order is preserved. None is the first element of the resulting list. *)

Definition toOptionList {X: Type} (A: list X) :=
  None :: map (@Some _) A .

(** This function counts the number of occurences of an element in a given list and returns the result *)
Fixpoint count (X: Type) `{eq_dec X}  (A: list  X) (x:  X) {struct A} : nat :=
  match A with
  | nil => O
  | cons y A' =>  if Dec (x=y) then S(count A' x) else count A' x end.

Definition toSumList1 {X: Type}  (Y: Type) (A: list X): list (X + Y) :=
  map inl A.
Definition toSumList2 {Y: Type}  (X: Type) (A: list Y): list (X + Y) :=
  map inr A.

(** * Basic lemmas about functions *)

(** In the list containing all pairs of (x,y') with y' from a list B the pair (x,y) is contained exactly as many times as y is contained in the list B. *)

Lemma countMap (X Y: eqType) (x:X) (B: list Y) y :
  count ( map (fun y => (x,y)) B) (x, y) = count B y.
Proof.
  induction B.
  - reflexivity.
  - simpl. dec;  congruence.
Qed.

(** If a list is split somewhere in two list the number of occurences of an element in the list is equal to the sum of the number of occurences in the left and the right part. *)

Lemma countSplit (X: eqType) (A B: list X) (x: X)  : count A x + count B x = count (A ++ B) x.
Proof.
  induction A.
  - reflexivity.
  - cbn. decide (x=a).
    +cbn. f_equal; exact IHA.
    + exact IHA.
Qed.

(** In a list of tupels with x as a left element the number of tupels with something different from x as a left element is 0. *)
Lemma countMapZero  (X Y: eqType) (x x':X) (B: list Y) y : x' <> x -> count  ( map (fun y => (x,y)) B) (x', y) =0.
Proof.
  intros ineq. induction B.
  - reflexivity.
  -  simpl. dec.
     + inversion e; congruence.
     + exact IHB.
Qed.


Lemma notInZero (X: eqType) (x: X) A :
  not (x el A) <-> count A x = 0.
Proof.
  split; induction A.
  -  reflexivity.
  - intros H. cbn in *. dec.
    + exfalso. apply H. left. congruence.
    + apply IHA. intros F. apply H. now right.
  - tauto.
  - cbn. dec.
    + subst a. omega.
    + intros H [E | E].
      * now symmetry in E.
      * tauto.
Qed.

Lemma countIn (X:eqType) (x:X) A:
  count A x > 0 -> x el A.
Proof.
  induction A.
  - cbn. omega.
  - cbn.  dec.
    + intros. left. symmetry. exact e.
    + intros. right. apply IHA. exact H.
Qed.

Lemma InCount (X:eqType) (x:X) A:
  x el A -> count A x > 0.
Proof.
  induction A.
  - intros [].
  - intros [[] | E]; cbn.
    + deq a. omega.
    + specialize (IHA E). dec; omega.
Qed.

Lemma count_in_equiv (X: eqType) (x:X) A : count A x > 0 <-> x el A.
Proof.
  split.
  - apply countIn.
  - apply InCount.
Qed.


Lemma countApp (X: eqType) (x: X) (A B: list X) :
  count (A ++ x::B) x > 0.
Proof.
  auto using InCount.
Qed.


(**  Dupfree Lists containing every x countain x exactly once *)
Lemma dupfreeCount (X: eqType) (x:X) (A: list X) : dupfree A -> x el A -> count A x = 1.
Proof.
  intros D E. induction D.
  -  contradiction E.
  - cbn. dec.
    + f_equal. subst x0. now apply notInZero.
    + destruct E as [E | E]; [> congruence | auto].
Qed.        

(** toSumlist1 does not change the number of occurences of an existing element in the list *)
Lemma toSumList1_count (X: eqType) (x: X) (Y: eqType) (A: list X) :
  count (toSumList1 Y A) (inl x) =  count A x .
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(** toSumlist2 odes not change the numbe of occurences of an existing element in the list *)
Lemma toSumList2_count (X Y: eqType) (y: Y) (A: list Y):
  count (toSumList2 X A) (inr y) = count A y.
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(** to sumList1 does not produce inr proofs *)
Lemma toSumList1_missing (X Y: eqType) (y: Y) (A: list X):
  count (toSumList1 Y A ) (inr y) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.

(** toSumlist2 does not produce inl proofs *)
Lemma toSumList2_missing (X Y: eqType) (x: X) (A: list Y):
  count (toSumList2 X A ) (inl x) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.


(** * Cardinality Lemmas for lists*)
Lemma cons_incll (X: Type) (A B: list X) (x:X) : x::A <<= B -> A <<= B.
Proof.
  unfold "<<=". auto.
Qed.

Lemma card_length_leq (X: eqType) (A: list X) : card A <= length A.
Proof.
  induction A; auto. cbn. dec; omega.
Qed.

(** * Various helpful Lemmas *)


(** If the concatenation of two lists is nil then each list was nil *)
Lemma appendNil (X: Type) (A B: list X) :
  A ++ B = nil -> A = nil /\ B = nil.
Proof.
  intros H. assert (|A ++ B| = 0) by now rewrite H.
  rewrite app_length in H0. rewrite <- !length_zero_iff_nil. omega.
Qed.

Lemma countZero (X: eqType) (x: X) (A: list X) : count A x = 0 -> not (x el A).
Proof.
  induction A; cbn in *; dec; firstorder congruence.
Qed.

(** The product of two numbers is greater zero if both numbers are greater zero *)
Lemma NullMul a b : a > 0 -> b > 0 -> a * b > 0.
Proof.
  induction 1; cbn; omega.
Qed.
