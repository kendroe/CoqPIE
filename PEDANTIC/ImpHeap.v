(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * ImpHeap.v
 * This file contains a model of the concrete state.  It was adapted from the
 * Software Foundations Imp.v model.
 *
 **********************************************************************************)

(* Based on work from http://www.seas.upenn.edu/~cis500/current/index.html *)

Require Export SfLib.
Require Export SfLibExtras.

(* ################################################### *)

(*
 * Concrete heap and environment state definitions
 *)

(* a cell is a struct -- a partial map of field ids to heap locations *)

Definition cell := id -> option nat.

(* heap is notated h in the paper *)

Definition heap := nat -> option nat.

(* env, a mapping of id's to heap locations, is notated s in the paper *)

Definition env := id -> nat.

Definition empty_env : env := fun _ => 0.

Definition empty_heap : heap := fun _ => None.

Definition empty_cell : cell := fun _ => None.

(* the overall execution state is an environment and a heap -- h,s in the paper *)

Definition state := prod env heap.

Definition empty_state : state := (empty_env,empty_heap).

Definition env_p (s : state) := fst s.

Definition heap_p (s : state) := snd s.


(* Basic operations on States *)

Definition override (st : env) (V:id) (n : nat) :=
  fun V' => if beq_id V V' then n else st V'.

Theorem override_eq : forall n V st,
  (override st V n) V = n.
Proof.
  intros n V st.
  unfold override.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.


Theorem override_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (override st V2 n) V1 = (st V1).
Proof.
    intros V2 V1 n st. unfold override. intros H. rewrite H. reflexivity. Qed.

Theorem override_shadow : forall x1 x2 k1 k2 (f : env),
   (override  (override f k2 x1) k2 x2) k1 = (override f k2 x2) k1.
Proof. intros x1 x2 k1 k2. intros f. unfold override. remember (beq_id k2 k1). destruct b. reflexivity. reflexivity. Qed.

Theorem override_same : forall x1 k1 k2 (f : env),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
    intros. unfold override. remember (beq_id k1 k2). destruct b. apply beq_id_eq in Heqb. subst. reflexivity.
    reflexivity.
Qed.

(*Theorem override_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false -> 
  (override (override f k2 x1) k1 x2) k3 = (override (override f k1 x2) k2 x1) k3.
Proof.*)

(* ################################################### *)

(* The programming language syntax is now defined *)

(* Arithmetic expressions *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AVar : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | AEq : aexp -> aexp -> aexp
  | ALe : aexp -> aexp -> aexp
  | ALand : aexp -> aexp -> aexp
  | ALor : aexp -> aexp -> aexp
  | ALnot : aexp -> aexp.

Tactic Notation "aexp_cases" tactic(firs) tactic(c) :=
  firs;
  [ c "ANum" | c "AVar" | c "APlus" | c "AMinus" | c "AMult" | c "AEq" |
    c "ALe" | c "ALand" | c "ALor" | c "ALnot" ].

(* Shorthand for common nats and nat operators *)

Notation A0 := (ANum 0).
Notation A1 := (ANum 1).
Notation A2 := (ANum 2).
Notation A3 := (ANum 3).
Notation A4 := (ANum 4).
Notation A5 := (ANum 5).
Notation A6 := (ANum 6).

Notation "a1 '***' a2" := (AMult a1 a2)
  (at level 50).

Notation "a1 '---' a2" := (AMinus a1 a2)
  (at level 40).

Notation "a1 '+++' a2" := (APlus a1 a2)
  (at level 40).

Notation "'!' X" := (AVar X)
  (at level 30).

Notation "b1 '===' b2" := (AEq b1 b2)
  (at level 60).

Notation "b1 '<<=' b2" := (ALe b1 b2)
  (at level 60).

(* Shorthand for common variable names *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(*
 * com is intended to mimic the constructs of a statement block in C or C++.
 *)
Inductive com : Type :=
  | CSkip : com
  | CLoad : id -> aexp -> com
  | CStore : aexp -> aexp -> com
  | CAss : id -> aexp -> com
  | CNew : id -> aexp -> com
  | CDelete: aexp -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : aexp -> com -> com -> com
  | CWhile : aexp -> com -> com
  | CCall : id -> id -> (list aexp) -> com
  | CReturn : aexp -> com
  | CThrow : id -> aexp -> com
  | CCatch : id -> id -> com -> com -> com.

Tactic Notation "com_cases" tactic(firs) tactic(c) :=
  firs;
  [ c "CSkip" | c "CLoad" | c "CStore" | c "CAss" | c "CNew" | c "CDelete" | c "CSeq" | c "CIf" | c "CWhile" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "l '::=' v '-->' i" :=
  (CLoad l v i) (at level 60).
Notation "l '-->' i '::=' v" :=
  (CStore l i v) (at level 60).
Notation "l '::=' a" := 
  (CAss l a) (at level 60).
Notation "'NEW' v , s" :=
  (CNew v s) (at level 60).
Notation "'DELETE' e ',' s" :=
  (CDelete e s) (at level 60).
Notation "'WHILE' b 'DO' c 'LOOP'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IF' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'RETURN' e" := (CReturn e) (at level 60).

(*
 * decl is intended look something like the AST for global declarations in C.
 *)
Inductive decl : Type :=
  | DGlobalVar : id -> decl
  | DFunction : id -> (list id) -> com -> decl.

(* Some example programs--This stuff should probably be deleted *)

(*Definition plus2 : com :=
  X ::= !X +++ A2.

Example plus2_notation :
  plus2 = 
  CAss (Id 0) (APlus (AVar (Id 0)) (ANum 2)).
Proof. reflexivity. Qed.*)

Definition XtimesYinZ : com :=
  Z ::= !X *** !Y.

(** loops *)
Definition subtract_slowly_body : com :=
  Z ::= !Z --- A1;
  X ::= !X --- A1.

Definition subtract_slowly : com :=
  WHILE ALnot (!X === A0) DO
    subtract_slowly_body
  LOOP.

Definition subtract_3_from_5_slowly : com :=
  X ::= A3;
  Z ::= A5;
  WHILE ALnot (!X === A0) DO
    subtract_slowly_body
  LOOP.

(* an infinite loop *)
Definition loop : com :=
  WHILE A1 DO
    SKIP
  LOOP.

(* factorial *)
Definition fact_body : com :=
  Y ::= !Y *** !Z;
  Z ::= !Z --- A1.

Definition fact_loop : com :=
  WHILE ALnot (!Z === A0) DO
    fact_body
  LOOP.

Definition fact_com : com :=
  Z ::= !X;
  Y ::= ANum 1;
  fact_loop.

(* exponentiation *)
Definition exp_body : com :=
    Z ::= !Z *** !X;
    Y ::= !Y --- A1.

Definition pexp : com :=
  WHILE ALnot (!Y === (ANum 0)) DO
    exp_body
  LOOP.

Definition add_body : com :=
  Y ::= !Y +++ !Z;
  Z ::= !Z --- A1.

Definition add_loop : com :=
  Z ::= A0;
  WHILE ALnot (!Z === A0) DO
    add_body
  LOOP.

Definition is_even_body : com :=
    Z ::= A1 --- !Z.

Definition is_even : com :=
  Z ::= A0;
  WHILE ALnot (!X === A0) DO
    is_even_body
  LOOP.

(* ################################################### *)

(* Now we will define what it means to evaluate a program *)

(* First, arithmetic evaluation *)

Fixpoint aeval (st : state) (e : aexp) {struct e} : nat :=
  match e with
  | ANum n => n
  | AVar i => (fst st) i
  | APlus a1 a2 => (plus (aeval st a1) (aeval st a2))
  | AMinus a1 a2 => (minus (aeval st a1) (aeval st a2))
  | AMult a1 a2 => (mult (aeval st a1) (aeval st a2))
  | AEq a1 a2 => if beq_nat (aeval st a1) (aeval st a2) then 1 else 0
  | ALe a1 a2 => if ble_nat (aeval st a1) (aeval st a2) then 1 else 0
  | ALnot a1 => if beq_nat (aeval st a1) 0 then 1 else 0
  | ALand a1 a2 => if beq_nat (aeval st a1) 0 then 0 else aeval st a2
  | ALor a1 a2 => if beq_nat (aeval st a1) 0 then aeval st a2 else (aeval st a1)
  end.

Fixpoint aeval_list (st : state) (e : list aexp) {struct e } : list nat :=
  match e with
  | nil => nil
  | (a::b) => (aeval st a)::(aeval_list st b)
  end.

(* Auxilliary functions needed for the evaluation relation *)

Definition bind_option (X Y : Type) (xo : option X) (f : X -> option Y) 
                      : option Y :=
  match xo with
    | None => None
    | Some x => f x
  end.

Implicit Arguments bind_option [X Y].

Fixpoint range (start : nat) (size : nat) (test : nat) { struct size } : bool :=
    match size with
      | 0 => false
      | S(s) => if beq_nat test (plus start s) then true
                else range start s test
    end.

(*Definition override_heap (h : heap) (V:nat) (c : option cell) :=
  fun V' => if beq_nat V V' then c else h V'.

Definition override_cell (c : cell) (V:id) (n : nat) :=
  fun V' => if beq_id V V' then Some n else c V'.*)

Inductive new_heap_cells : heap -> nat -> nat -> heap -> Prop :=
  | OHDone : forall h v,
             new_heap_cells h v 0 h
  | OHNext : forall h h' v c val h'',
             new_heap_cells h (S v) c h' ->
             h' v = None ->
             h'' = (fun x => if beq_nat x v then Some val else h' x) ->
             new_heap_cells h v (S c) h''.

Inductive clear_heap_cells : heap -> nat -> nat -> heap -> Prop :=
  | CHDone : forall h v,
             clear_heap_cells h v 0 h
  | CHNext : forall h h' v c val h'',
             clear_heap_cells h (S v) c h' ->
             h' v = Some val ->
             h'' = (fun x => if beq_nat x v then None else h' x) ->
             clear_heap_cells h v (S c) h''.

Inductive result : Type :=
  | NoResult : result
  | Return : nat -> result
  | Exception : id -> nat -> result.

(*
 * This type is used to specify the behavior of functions.  It is needed to implement the semantics
 * of function calls.
 *)
Definition functions := id -> state -> (list nat) -> state -> result -> Prop.

(* Finally, the inductive definition of evaluation of commands, giving meaning
   of concrete execution.  This is relation s, h --c--> c', h' in the paper.  This definition
   gives semantics for both the loading and saving of data to the heap in addition to basic
   operations.  We also give semantics for function calls, a return statement and catch/throw.
   However, these operators are not being used in the abstract model at the current time.

 *)

Inductive ceval : functions -> state -> com -> state -> result -> Prop :=
  | CESkip : forall f st,
      ceval f st CSkip st NoResult
  | CEAss  : forall f st a1 l,
      ceval f st (CAss l a1) ((override (fst st) l (aeval st a1)),(snd st)) NoResult
  | CENew : forall f st l loc e count h',
      (not (loc=0)) ->
      count = aeval st e ->
      new_heap_cells (snd st) loc count h' ->
      ceval f st (CNew l e) (override (fst st) l loc,h') NoResult
  | CEDelete : forall f st loc count l c h',
      l = aeval st loc ->
      c = aeval st count ->
      clear_heap_cells (snd st) l c h' ->
      ceval f st (CDelete loc count) (fst st,h') NoResult
  | CELoad : forall f st loc l val,
      Some val = (snd st) (aeval st loc) ->
      ceval f st (CLoad l loc) ((override (fst st) l val),(snd st)) NoResult
  | CEStore : forall f st loc val l v ov,
      v = aeval st val ->
      l = aeval st loc ->
      (snd st) l = Some ov ->
      ceval f st (CStore loc val) ((fst st),(fun x => if beq_nat l x then (Some v) else (snd st) x)) NoResult
  | CESeq1 : forall f c1 c2 st st' st'' r,
      ceval f st c1 st' NoResult ->
      ceval f st' c2 st'' r ->
      ceval f st (CSeq c1 c2) st'' r
  | CESeq2 : forall f c1 c2 st st' v,
      ceval f st c1 st' (Return v) ->
      ceval f st (CSeq c1 c2) st' (Return v)
  | CESeq3 : forall f c1 c2 st st' name val,
      ceval f st c1 st' (Exception name val) ->
      ceval f st (CSeq c1 c2) st' (Exception name val)
  | CEIfTrue : forall f r st st' b1 c1 c2,
      not(aeval st b1 = 0) ->
      ceval f st c1 st' r ->
      ceval f st (CIf b1 c1 c2) st' r
  | CEIfFalse : forall f r st st' b1 c1 c2,
      aeval st b1 = 0 ->
      ceval f st c2 st' r ->
      ceval f st (CIf b1 c1 c2) st' r
  | CEWhileEnd : forall f b1 st c1,
      aeval st b1 = 0 ->
      ceval f st (CWhile b1 c1) st NoResult
  | CEWhileLoop1 : forall f st st' st'' b1 c1 r,
      not(aeval st b1 = 0) ->
      ceval f st c1 st' NoResult ->
      ceval f st' (CWhile b1 c1) st'' r ->
      ceval f st (CWhile b1 c1) st'' r
  | CEWhileLoop2 : forall f st st' b1 c1 r,
      not(aeval st b1 = 0) ->
      ceval f st c1 st' (Return r) ->
      ceval f st (CWhile b1 c1) st' (Return r)
  | CEWhileLoop3 : forall f st st' b1 c1 name val,
      not(aeval st b1 = 0) ->
      ceval f st c1 st' (Exception name val) ->
      ceval f st (CWhile b1 c1) st' (Exception name val)
  | CEThrow: forall f st val exp v,
      val = aeval st exp ->
      ceval f st (CThrow v exp) st (Exception v val)
  | CECatch1: forall f st st' exc var code hand,
      ceval f st code st' NoResult ->
      ceval f st (CCatch exc var code hand) st' NoResult
  | CECatch2: forall f st st' exc var code hand v,
      ceval f st code st' (Return v) ->
      ceval f st (CCatch exc var code hand) st' (Return v)
  | CECatch3: forall f st st' exc var code hand v name,
      ceval f st code st' (Exception name v) ->
      name <> exc ->
      ceval f st (CCatch exc var code hand) st' (Exception name v)
  | CECatch4: forall f st st' exc var code hand v name st'' r,
      ceval f st code st' (Exception exc v) ->
      ceval f (override (fst st') var v,(snd st')) hand st'' r ->
      name <> exc ->
      ceval f st (CCatch exc var code hand) st'' r
  | CECall1: forall vl st el (f:functions) (st':state) r (fid:id) var,
      vl = aeval_list st el ->
      f fid st vl st' (Return r) ->
      ceval f st (CCall var fid el) (override (fst st') var r,(snd st')) NoResult
  | CECall2: forall vl st el (f:functions) (st':state) r (fid:id) var name,
      vl = aeval_list st el ->
      f fid st vl st' (Exception name r) ->
      ceval f st (CCall var fid el) st' (Exception name r).



 


