Require Export Induction.
Module NatList.

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint snoc (l:natlist) (x:nat) : natlist :=
  match l with
  | nil => x :: nil
  | h :: t => h :: (snoc t x)
  end.
                  
(* Exercise: Define the "member" function on natlists *)
Fixpoint member (l:natlist) (x:nat) : bool := admit.

(* Prove the following three theorems. Looking at them: Which do you
need to use induction on? Which require destruct (only)? Which require
only intros and reflexivity? *)

Theorem member_in_cons : forall (l : natlist) (x : nat),
  member (x :: l) x = true.
Proof. Admitted.

Theorem member_not_in_nil : forall (x : nat),
  member (nil) x = false.
Proof. Admitted.

Theorem snoc_plus_one : forall (x : nat) (l : natlist),
  length (snoc l x) = 1 + (length l).
Proof. Admitted.

(* To do: Quick visit of PartialMap from Lists.v *)

