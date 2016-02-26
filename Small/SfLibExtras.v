(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * SfLibExtras.v
 * This file contains a few theorems to supplement what is available in SfLib.v
 *
 **********************************************************************************)

Require Export SfLib.

(* Simple auxiliary list functions for lists of id's/nats *)

(* Identifiers and equivalence thereupon; used both for variables, Var/Var', 
   and field names, Fld, from the paper *)

Inductive id : Type := 
  | Id : nat -> id
  | PrimedId : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    | (Id n1, Id n2) => beq_nat n1 n2
    | (PrimedId n1, PrimedId n2) => beq_nat n1 n2
    | _ => false
    end.

Definition ble_id id1 id2 :=
  match (id1, id2) with
    | (Id n1, Id n2) => ble_nat n1 n2
    | (PrimedId n1, PrimedId n2) => ble_nat n1 n2
    | (PrimedId n1, Id n2) => true
    | _ => false
    end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  unfold beq_id. apply beq_nat_refl.  unfold beq_id. apply beq_nat_refl. Qed.

Theorem beq_nat_comm : forall a b,
    beq_nat a b = beq_nat b a.
Proof.
    intro a. induction a. destruct b. simpl. reflexivity. simpl. reflexivity. intros.
    destruct b. simpl. reflexivity. simpl. apply IHa.
Qed.

Theorem beq_id_comm : forall a b,
    beq_id a b = beq_id b a.
Proof.
    destruct a. destruct b. unfold beq_id. apply beq_nat_comm.
    simpl. unfold beq_id. reflexivity.
    intros. destruct b. unfold beq_id. reflexivity. unfold beq_id. apply beq_nat_comm.
Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof. intros i1 i2. destruct i1. destruct i2. unfold beq_id. intros H. apply beq_nat_eq in H. rewrite H. reflexivity. unfold beq_id. intros H. inversion H. destruct i2. unfold beq_id. intros H. inversion H. unfold beq_id. intros H. apply beq_nat_eq in H. rewrite H.  reflexivity. Qed.

Theorem beq_nat_neq:
    forall a b, false=(beq_nat a b) -> (a<>b).
Proof.
    induction a.
        intros. destruct b. unfold beq_nat in H. inversion H.
        intro X. inversion X.

        intros. destruct b. intro X. inversion X.
        intro X. inversion X. subst. simpl in H. rewrite <- beq_nat_refl in H. inversion H.
Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
    destruct i1. destruct i2.
        unfold beq_id. intros.
    intros. assert (false = beq_nat n n0). rewrite H. reflexivity.
    apply beq_nat_neq in H0. intro X. inversion X. rewrite H2 in H0. elim H0. reflexivity.
    intro. intro X. inversion X.

    destruct i2. intros. intro X. inversion X.
    intros. unfold beq_id in H. assert (false = beq_nat n n0). rewrite H. reflexivity.
    apply beq_nat_neq in H0. intro X. inversion X. rewrite H2 in H0. elim H0. reflexivity.
Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof. destruct i1. destruct i2. unfold beq_id. intros H. apply not_eq_beq_false. unfold not. intros H1. rewrite H1 in H. unfold not in H. clear H1. apply H. reflexivity. intros H. unfold beq_id.  reflexivity. intros i2. destruct i2. intros H. unfold beq_id. reflexivity. unfold beq_id. intros H. apply not_eq_beq_false. unfold not. intros H1. rewrite H1 in H. unfold not in H. clear H1. apply H. reflexivity. Qed.


Fixpoint mem_id (e : id) (l : list id) { struct l } : bool :=
    match l with
        | (f::r) => if beq_id f e then true else mem_id e r
        | Nil    => false
    end.

Fixpoint mem_nat (e : nat) (l : list nat) { struct l } : bool :=
    match l with
        | (f::r) => if beq_nat f e then true else mem_nat e r
        | Nil    => false
    end.

Fixpoint merge (l1 : list id) (l2 : list id) { struct l1 } : list id :=
    match l1 with
       | a::b => if mem_id a l2 then merge b l2 else a::(merge b l2)
       | Nil => l2
    end.

Theorem beq_nat_eq:
    forall a b, true=(beq_nat a b) -> a=b.
Proof.
    intro a. induction a.
        intros. destruct b. reflexivity. unfold beq_nat in H. inversion H. intros. destruct b. unfold beq_nat in H. inversion H.
        unfold beq_nat in H. simpl. fold beq_nat in H. apply IHa in H. rewrite H. reflexivity.
Qed.

(*Theorem beq_nat_helper: forall a b,
    S a <> S b -> a <> b.
Proof. admixt. Qed.

Theorem beq_nat_bad :
    forall a b,
    a <> b ->
    beq_nat a b=false.
Proof.
    intro a. induction a.
        intros. destruct b. elim H. reflexivity. simpl. reflexivity.
        intros. destruct b. simpl. reflexivity. simpl. apply IHa. apply beq_nat_helper in H. apply H.
Qed.*)

Theorem beq_nat_same :
    forall a, beq_nat a a = true.
Proof.
    intro a. induction a. simpl. reflexivity. simpl. apply IHa.
Qed.
