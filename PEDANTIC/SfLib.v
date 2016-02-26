(** * SfLib: Software Foundations Library *)
(* Version of 10/14/2009 *)


(* ###################################################################### *)
(** Here we collect together several useful definitions and theorems from
   Basics, List, Poly, Props, and Logic that are not already in the Coq
   standard library. From now on we can [Import] or [Export] this file, instead of
   using all the examples and false starts in those files. *)

(** * From the Coq standard library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name :=  Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
    intros. destruct b. simpl in H. apply H.
    simpl in H. inversion H.
Qed.

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n'
  -> beq_nat n n' = false.
Proof.
    induction n.
        intros. destruct n'. elim H. reflexivity.
        simpl. reflexivity.

        intros. destruct n'.
            simpl. reflexivity.

            simpl. apply IHn.

            intro H'. rewrite H' in H. elim H. reflexivity.
Qed.

(*Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  induction n.
  intros. simpl. unfold ev.
xdmitted.*)
(* An exercise in Logic.v *)

(*Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.

  induction n.
      intros. omega.

      intros. destruct m. simpl in H. inversion H.

      simpl in H.
 An exercise in Logic.v 
xdmitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
 An exercise in Logic.v 
xdmitted.
*)
(** This is not identical to the [partial_function] in Logic.v,
   because it permits the domain type [X] and the range type [Y]
   to be different.  The curly braces around
     [{X Y: Type}] are a concise way of saying 
       [Implicit Arguments] for [X] and [Y]. *)

Definition partial_function {X Y: Type} (R: X -> Y -> Prop) :=
  forall (x: X) (y1 y2 : Y), R x y1 -> R x y2 -> y1 = y2.

(* Basic list functions *)


Fixpoint sameLength (X : Type) (Y : Type) (a : list X) (b : list Y) : Prop :=
    match a with
     | nil => b=nil
     | (_::r1) => match b with
                   | nil => False
                   | (_::r2) => sameLength X Y r1 r2
                  end
   end.

Implicit Arguments sameLength [X Y].

Fixpoint elementPair (X : Type) (Y : Type) (a : X) (b : Y) (l1 : list X) (l2 : list Y) : Prop :=
    match l1 with
     | nil => False
     | (x::r1) => match l2 with
                   | nil => False
                   | (y::r2) => (x=a /\ y=b) \/ elementPair X Y a b r1 r2
                  end
    end.

Implicit Arguments elementPair [X Y].

Fixpoint elementTriple (X : Type) (Y : Type) (Z : Type) (a : X) (b : Y) (c : Z) (l1 : list X) (l2 : list Y) (l3 : list Z) : Prop :=
    match l1 with
     | nil => False
     | (x::r1) => match l2 with
                   | nil => False
                   | (y::r2) => match l3 with
                                 | nil => False
                                 | (z::r3) => (x=a /\ y=b /\ z=c) \/ elementTriple X Y Z a b c r1 r2 r3
                                end
                  end
    end.

Implicit Arguments elementTriple [X Y Z].
