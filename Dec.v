Require Import Prelim.

(** De Morgan laws *)

Lemma DM_or (X Y : Prop) :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  tauto.
Qed.

Lemma DM_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.

(** ** Boolean propositions and decisions *)

Coercion bool2Prop (b : bool) := if b then True else False.

Lemma bool_Prop_true b :
  b = true -> b.
Proof.
  intros A. rewrite A. exact I.
Qed.

Lemma bool_Prop_false b :
  b = false -> ~ b.
Proof.
  intros A. rewrite A. cbn. auto.
Qed.

Hint Resolve bool_Prop_true bool_Prop_false.

Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: ~ bool2Prop true |- _ ] => destruct H
|[ H: bool2Prop false |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
|[ H: ?b=false, H': bool2Prop(?b) |- _ ] => rewrite H in H'; destruct H'
|[ H: ?x el nil |- _ ] => destruct H
end.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.


Lemma Dec_reflect (X: Prop) (d: dec X) :
  Dec X <-> X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Notation Decb X := (dec2bool (Dec X)).

Lemma Dec_reflect_eq (X Y: Prop) (d: dec X) (e: dec Y) :
 Decb X = Decb Y <->  (X <-> Y).
Proof.
  destruct d as [D|D], e as [E|E]; cbn; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Lemma Dec_auto_not (X: Prop) (d: dec X) :
  ~ X -> ~ Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Hint Resolve Dec_auto Dec_auto_not.
Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).
Tactic Notation "have" constr(E) := let X := fresh "E" in decide E as [X|X]; subst; try congruence; try omega; clear X.

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = false |- _ ] => apply Dec_false in H
end.

(** Decided propositions behave classically *)

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

(** Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance bool_dec (b: bool) :
  dec b.
Proof. 
  unfold dec. destruct b; cbn; auto. 
Qed.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Qed.

Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Qed.

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Qed.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Qed.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Qed.

(** ** Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.

Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Qed.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Qed.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Qed.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Qed.
