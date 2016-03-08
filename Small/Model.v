(**********************************************************************************
 *
 * Model.v
 *
 * A Small Coq model
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.

Inductive Exp :=
  | Var : nat -> Exp
  | Const : nat -> Exp
  | Plus : Exp -> Exp -> Exp
  | Times : Exp -> Exp -> Exp
  (*| Ref : Exp -> Exp*)
  | Find : Exp -> Exp
  | Ite : Exp -> Exp -> Exp -> Exp.

Fixpoint findit a l :=
    match l with
    | nil => 0 
    | (f::r) => if beq_nat a f then (S 0) else match findit a r with
                                               | 0 => 0
                                               | (S n) => S (S n)
                                               end
    end. 
         
Fixpoint eval e l := 
         match e with
         | Const v => v 
         | Var n => nth n l 0
         | Plus a b => (eval a l)+(eval b l)
         | Times a b => (eval a l)+(eval b l)
         (*| Ref a => nth (eval a l) l 0*)
         | Find a => findit (eval a l) l
         | Ite a b c => match (eval a l) with
                        | 0 => eval c l
                        | S _ => eval b l
                        end
         end.

Fixpoint pop e v :=
         match e with
         | Const v => Const v
         | Var 0 => Const v
         | Var (S n) => Var n
         | Plus a b => Plus (pop a v) (pop b v)
         | Times a b => Times (pop a v) (pop b v)
         (*| Ref a => Ref (pop a v)*)
         | Find e => Find (pop e v)
         | Ite a b c => Ite (pop a v) (pop b v) (pop c v)
         end.

Fixpoint noFind e :=
    match e with
    | Const _ => true
    | Var _ => true
    | Plus a b => if noFind a then noFind b else false
    | Times a b => if noFind a then noFind b else false
    (*| Ref e => noFind e*)
    | Find e => false
    | Ite a b c => if noFind a then (if noFind b then noFind c else false) else false
    end.

(*Fixpoint noRef e :=
    match e with
    | Const _ => true
    | Var _ => true
    | Plus a b => if noRef a then noRef b else false
    | Times a b => if noRef a then noRef b else false
    | Ref e => false
    | Find e => noRef e
    | Ite a b c => if noRef a then (if noRef b then noRef c else false) else false
    end.*)

Theorem popEquiv : forall e v l, (* noRef e=true -> *) noFind e=true -> eval e (v::l)=eval (pop e v) l.
Proof.
    intro e.
    induction e.

    simpl. unfold eval. destruct n. reflexivity. reflexivity.

    unfold pop. unfold eval. reflexivity.

    intros. unfold noFind in H. fold noFind in H.  remember (noFind e1). destruct b.

    unfold pop. fold pop. unfold eval. fold eval.

    rewrite IHe1. rewrite IHe2.
    reflexivity. apply H. reflexivity. inversion H.


    intros. unfold noFind in H. fold noFind in H.  remember (noFind e1). destruct b.

    unfold pop. fold pop. unfold eval. fold eval.

    rewrite IHe1. rewrite IHe2.
    reflexivity. apply H. reflexivity. inversion H.

    intros. unfold noFind in H. inversion H.

    intros. unfold noFind in H. fold noFind in H. remember (noFind e1). destruct b.
    destruct (noFind e2).

    unfold pop. fold pop. unfold eval. fold eval.

    rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.

    apply H. reflexivity. reflexivity. inversion H. inversion H.
Qed.

Inductive Pr :=
          | Atom : Exp -> Pr
          | And : Pr -> Pr -> Pr
          | Or : Pr -> Pr -> Pr
          | Implies : Pr -> Pr -> Pr.

Fixpoint valid p l :=
    match p with
    | Atom e => if beq_nat (eval e l) 0 then false else true
    | And a b => if valid a l then valid b l else false
    | Or a b => if valid a l then true else valid b l
    | Implies a b => if valid a l then valid b l else true
    end.

Theorem validTransitive : forall a b c, (a -> b) -> (b -> c) -> (a ->c).
Proof.
    intros.

    apply X0. apply X. apply X1.
Qed.

Theorem and1imply : forall a b l, (valid (And a b) l)=true -> valid a l=true.
Proof.
    intros.

    unfold valid in H. fold valid in H.

    destruct (valid a l). reflexivity. inversion H.
Qed.

Theorem and2imply : forall a b l, (valid (And a b) l)=true -> valid b l=true.
Proof.
    intros. unfold valid in H. fold valid in H.

    destruct (valid a l). apply H. inversion H.
Qed.

Inductive pickElement : Pr -> Pr -> Pr -> Prop :=
    | Left : forall a b l r, pickElement a l r -> pickElement (And a b) (And l b) r
    | Right : forall a b l r, pickElement b l r -> pickElement (And a b) (And a l) r
    | Pick : forall a b, a=b -> pickElement a (Atom (Const 1)) a.

Theorem mergeStep : forall X XX Y YY l e1 e2 Q,
    pickElement X XX e1 ->
    pickElement Y YY e2 ->
    e1=e2 ->
    (valid XX l=true \/ valid YY l=true -> valid Q l=true) ->
    (valid X l=true \/ valid Y l=true -> valid (And e2 Q) l=true).
Proof.
    admit.
Qed.

Theorem mergeFinish: forall l, valid (Atom (Const 1)) l=true.
Proof.
    admit.
Qed.

Theorem mergePredicates: forall e a b c d l,
    e = b ->
    valid (And a (And e c)) l=true \/
    valid (And b d) l=true ->
    valid b l=true.
Proof.
    intros e a b c d l.
    eapply validTransitive.
    eapply mergeStep.
        eapply Right. eapply Left. eapply Pick. reflexivity.
        eapply Left. eapply Pick. reflexivity. apply H.
    intros. eapply mergeFinish.

    intros. eapply and1imply. apply H0.
Qed.


