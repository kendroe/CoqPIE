(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * AbsState.v
 * This file contains a model of the abstract state template.  The function realizeState relates
 * these abstract states to concrete states.  Key top level
 * definitions:
 *    Value
 *    absExp
 *    absState
 *    absEval
 *    realizeState
 *    supportsFunctionality
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export ImpHeap.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Tactics.

(* This file implements the data types and operations on the abstract state,
   the \Pi | \Sigma of the paper. *)


(*******************************************************************************
 *
 * absHeap, the abstract heaps
 *
 *******************************************************************************)

Definition stateProp := state -> Prop.

(******************************************************************************
 *
 * This section builds up the definition of composing abstract states.
 *
 ******************************************************************************)

Definition compose_heaps (h1 : heap) (h2 : heap) (x : nat) :=
    match h1 x with
      | None => h2 x
      | Some x => Some x
    end.

Definition concreteCompose (s1 : state) (s2 : state) (s : state) : Prop :=
    (fst s1)=(fst s2) /\
    (fst s)=(fst s1) /\
    (forall v, (snd s1) v=None \/ (snd s2) v=None) /\
    compose_heaps (snd s1) (snd s2)=(snd s).

Theorem composeEnvPropagate1 :
    forall s1 s2 s v,
    concreteCompose s1 s2 s ->
    fst s1 v = fst s v.
Proof.
    unfold concreteCompose. intros. inversion H. clear H. inversion H1. clear H1. rewrite H. reflexivity.
Qed.

Theorem composeEnvPropagate2 :
    forall s1 s2 s v,
    concreteCompose s1 s2 s ->
    fst s2 v = fst s v.
Proof.
    unfold concreteCompose.
    intros. inversion H. clear H. inversion H1. clear H1. rewrite H. rewrite H0. reflexivity.
Qed.
(*
 * This is the main definition for composing abstract states
 *)
Definition composeAbsStates (as1 : stateProp) (as2 : stateProp) : stateProp :=
        (fun x => match x with
                      (b,h) => exists h1, exists h2,
                           as1 h1 /\
                           as2 h2 /\
                           (forall v, ((snd h1) v=None \/ (snd h2) v=None)) /\
                           (fst h1)=(fst h2) /\
                           (forall x, h x = compose_heaps (snd h1) (snd h2) x)
                  end).

(******************************************************************************
 *
 * This section builds up the definition of absState and contains a few
 * functions for returning information about absState objects.
 *
 ******************************************************************************)

Definition absVar := nat.

Definition absHeap h hpred := (fun (x : state) => (h = (snd x) /\ hpred (snd x) /\ (forall v, fst x v=0))).

Definition bind {ev} := nat -> option ev.

(*Definition evType := fst.*)

(* Value is the type used for the values returned when evaluating an absExp *)
Inductive Value {ev} : Type :=
    | NatValue : nat -> Value
    | ListValue : list Value -> Value
    | NoValue : Value
    | OtherValue : ev -> Value.

(* Here is the definition for expressions.
 * It takes three parameters in defining its semantics:
 *     ev - the type of the OtherType case in Value
 *     eq - an equality function over ev
 *     f - a function defining the semantics of AbsFun--this usually includes definitions for
 *         many basic operators such as addition
 *)
Inductive absExp (*{ev} {eq : ev -> ev -> bool}
                 { f : id -> list (@Value ev) -> (@Value ev) }*) : Type :=
   | AbsConstVal : (@Value unit) -> absExp
   | AbsVar : id -> absExp
   | AbsQVar : absVar -> absExp
   | AbsFun : id -> list absExp -> absExp.

(* *****************************************************************************************
 * We need to create a specialized induction principle for absExp.  Without it, no inductive
 * hypothesis will show up in the AbsFun case for proofs that use induction over the absExp
 * type.
 *)
Fixpoint All {T} (P : T -> Prop) (ls : list T) : Prop :=
    match ls with
    | nil => True
    | (h::t) => P h /\ All P t
    end.

Fixpoint abs_ind' (*{ev} {eq : ev -> ev -> bool} { f : id -> list (@Value ev) -> (@Value ev) }*)
                  (P : absExp -> Prop)
                  (cbase : forall c, P (AbsConstVal c))
                  (vbase : forall id, P (AbsVar id))
                  (qbase : forall v, P (AbsQVar v))
                  (ff : forall id l, (All P l) -> P (AbsFun id l))
                  (e : absExp) : P e :=
    match e with
    | (AbsConstVal c) => cbase c
    | (AbsVar i) => vbase i
    | (AbsQVar v) => qbase v
    | (AbsFun i l) => ff i l
      ((fix go (ll : list absExp) : All P ll := match ll return All P ll with
                   | (fff::r) => conj (abs_ind' P cbase vbase qbase ff fff) (go r)
                   | nil => I
                   end) l)
    end.

Fixpoint value_ind' (*{ev}*)
                  (P : @Value unit -> Prop)
                  (nabase : forall c, P (NatValue c))
                  (nobase : P NoValue)
                  (obase : forall v, P (OtherValue v))
                  (ff : forall l, (All P l) -> P (ListValue l))
                  (e : @Value unit) : P e :=
    match e with
    | (NatValue n) => nabase n
    | NoValue => nobase
    | (OtherValue v) => obase v
    | (ListValue l) => ff l
      ((fix go (ll : list (@Value unit)) : All P ll := match ll return All P ll with
                   | (fff::r) => conj (value_ind' P nabase nobase obase ff fff) (go r)
                   | nil => I
                   end) l)
    end.

(* This theorem help us break down the All construct in proofs. *)
Theorem reduceAll : forall T P ls, @All T P ls -> (forall x:T, In x ls -> P x).
Proof.
    intro. intro. intro. induction ls.

    simpl. intros. inversion H0.

    simpl. intros.
    inversion H. subst. clear H.
    inversion H0. subst. apply H1. apply IHls. apply H2. apply H.
Qed.

(*
 * Here is some equality definitions for values and expressions
 *)
Definition beq_list {A} (f : A -> A -> bool) : list A -> list A -> bool :=
 fix go l k :=
 match l, k with
 | nil, nil => true
 | x :: l, y :: k => f x y && go l k
 | _, _ => false
 end.

Fixpoint beq_val (*{t} {eq}*) (e1 : @Value unit) (e2 : @Value unit) : bool :=
    match (e1,e2) with
    | (NatValue v1,NatValue v2) => beq_nat v1 v2
    | (ListValue l1,ListValue l2) => beq_list (beq_val) l1 l2
    | (NoValue,NoValue) => true
    | (OtherValue v1,OtherValue v2) => true
    | _ => false
    end.

Fixpoint beq_absExp (*{ev} {eq} {x}*) (e1 : absExp) (e2 : absExp) : bool :=
   match e1 with
   | (AbsConstVal v) => match e2 with (AbsConstVal v2) => beq_val v v2 | _ => false end
   | (AbsQVar v) => match e2 with (AbsQVar v2) => beq_nat v v2 | _ => false end
   | (AbsVar v) => match e2 with (AbsVar v2) => beq_id v v2 | _ => false end
   | (AbsFun id1 l1) => match e2 with
                        | (AbsFun id2 l2) => beq_id id1 id2 &&
                                             beq_list (beq_absExp) l1 l2
                        | _ => false
                        end
   end.

Notation "'!!' x" :=(AbsVar x) (at level 1).
Notation "'v(' n ')'" := (AbsQVar n)
  (at level 1).

Notation "'#' n" := (AbsConstVal (NatValue n))
  (at level 1).

Inductive strip_option {x} : list (option x) -> list x -> Prop :=
   | SONil : strip_option nil nil
   | SOCons : forall f r r',
              strip_option r r' ->
              strip_option ((Some f)::r) (f::r').

(***************************************************************************
 *
 * basicEval
 *
 * This is used to fill in the 'f' parameter in absExp.
 *
 ***************************************************************************)

Notation "'AbsNthId'" := (Id 1) (at level 1).
Notation "'AbsPlusId'" := (Id 2) (at level 1).
Notation "'AbsMinusId'" := (Id 3) (at level 1).
Notation "'AbsTimesId'" := (Id 4) (at level 1).
Notation "'AbsEqualId'" := (Id 5) (at level 1).
Notation "'AbsLessId'" := (Id 6) (at level 1).
Notation "'AbsMemberId'" := (Id 7) (at level 1).
Notation "'AbsIncludeId'" := (Id 8) (at level 1).
Notation "'AbsImplyId'" := (Id 9) (at level 1).
Notation "'AbsNotId'" := (Id 10) (at level 1).
Notation "'AbsAndId'" := (Id 11) (at level 1).
Notation "'AbsOrId'" := (Id 12) (at level 1).
Notation "'AbsIteId'" := (Id 13) (at level 1).
Notation "'AbsFindId'" := (Id 14) (at level 1).
Notation "'AbsListId'" := (Id 15) (at level 1).
Notation "'AbsRangeSetId'" := (Id 16) (at level 1).
Notation "'AbsRangeNumericId'" := (Id 17) (at level 1).
Notation "'AbsReplaceNthId'" := (Id 18) (at level 1).

Fixpoint rangeSet {t} (v : @Value t) : @Value t :=
  match v with
  | (ListValue (NatValue loc::r)) =>
            (fix go (x : (list (@Value t))) :=
                    match x with
                    | (f::l) => match (rangeSet f,go l) with
                                | ((ListValue l),(ListValue y)) => (ListValue (l++y))
                                | _ => NoValue
                                end
                    | _ => (ListValue nil)
                    end) r
  | (NatValue _) => (ListValue nil)
  | _ => NoValue
  end.

Fixpoint numericRange {t} (s : nat) (e : nat) : @Value t :=
    if beq_nat s e then (ListValue nil)
    else match e with
         | 0 => (ListValue (nil))
         | (S e') => match numericRange s e' with
                     (ListValue l) => (ListValue (l++((NatValue e')::nil)))
                     | _ => NoValue
                     end
         end.

Fixpoint replacenth {t} (l : list t) (n : nat) (e : t) :=
    match l,n with
    | (f::r),0 => (e::r)
    | (f::r),(S n1) => (f::(replacenth r n1 e))
    | l,_ => l
    end.

Fixpoint flatten {t} (v : @Value t) (loc : nat) : list ((@Value t) * nat) :=
    match v with
    | (ListValue ((NatValue loc)::ll)) =>
        (v,loc)::((fix go (x : list (@Value t)) l :=
             match x with
             | (f::r) => (flatten f l)++(go r (l+1))
             | _ => nil
             end) ll loc)
    | x => (v,loc)::nil
    end.

Fixpoint rmemberFullList {t} (n : nat) (v : (list ((@Value t) * nat))) : bool :=
    match v with
    | ((val,loc)::r) => if beq_nat loc n then true else rmemberFullList n r
    | _ => false
    end.

Fixpoint rmemberList {t} (n : nat) (v : (list ((@Value t) * nat))) : bool :=
    match v with
    | ((ListValue ((NatValue xx)::ll),loc)::r) => if beq_nat loc n then true else rmemberList n r
    | (_::r) => rmemberList n r
    | _ => false
    end.
Definition Rmember {t} (l : nat) (tree : @Value t) : bool :=
    rmemberList l (flatten tree 0).

Definition Rinclude {t} (l : nat) (tree : @Value t) : bool :=
    rmemberFullList l (flatten tree 0).

Fixpoint findRecord {t} (l : nat) (v : @Value t) :=
    match v with
    | (ListValue ((NatValue x)::r)) =>
                 if beq_nat x l then
                     ((NatValue x)::r)
                 else (fix go ll :=
                          match ll with
                          | nil => nil
                          | (f::r) => match findRecord l f with
                                      | nil => go r
                                      | x => x
                                      end
                          end) r
    | _ => nil
    end.

(*
 * Rinclude is the same as Rmember except that it tests whether the location is a pointer to
 * any cell within a node rather than just the first.  It is used for 'inTreeLoc' defined in
 * basicEval
 *
 * Parameters:
 *    l - location to test
 *    tree - a tree (which is the same form as parameter #4 to tree above
 *)
Fixpoint basicEval (op : id) (args : list (@Value unit)) : @Value unit :=
    match (op,args) with
    | (AbsNthId,((ListValue l)::(NatValue f)::nil)) => nth f l NoValue
    | (AbsPlusId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l+r))
    | (AbsMinusId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l-r))
    | (AbsTimesId,((NatValue l)::(NatValue r)::nil)) => (NatValue (l*r))
    | (AbsEqualId,((NatValue l)::(NatValue r)::nil)) => if beq_nat l r then (NatValue 1) else (NatValue 0)
    | (AbsLessId,((NatValue l)::(NatValue r)::nil)) => if ble_nat r l then (NatValue 0) else (NatValue 1)
    | (AbsMemberId,((NatValue l)::tree::nil)) => if Rmember l tree then (NatValue 1) else (NatValue 0)
    | (AbsIncludeId,((NatValue l)::tree::nil)) => if Rinclude l tree then (NatValue 1) else (NatValue 0)
    | (AbsImplyId,((NatValue l)::r::nil)) => if beq_nat l 0 then NatValue 1 else r
    | (AbsNotId,((NatValue l)::nil)) => if beq_nat l 0 then NatValue 1 else NatValue 0
    | (AbsAndId,((NatValue l)::r::nil)) => if beq_nat l 0 then NatValue 0 else r
    | (AbsOrId,((NatValue l)::r::nil)) => if beq_nat l 0 then r else (NatValue l)
    | (AbsIteId,((NatValue c)::t::e::nil)) => if beq_nat c 0 then e else t
    | (AbsFindId,(v::(NatValue x)::nil)) => ListValue (@findRecord unit x v)
    | (AbsListId,l) => @ListValue unit l
    | (AbsRangeSetId,(f::nil)) => rangeSet f
    | (AbsRangeNumericId,((NatValue s)::(NatValue e)::nil)) => numericRange s e
    | (AbsReplaceNthId,((ListValue l)::(NatValue n)::e::nil)) => (ListValue (replacenth l n e))
    | _ => NoValue
    end.

(* ************************************************************************************
 * Definition of expression evaluation--note how the "f" parameter of absExp is used to
 * define the semantics of absFun.
 *
 * Parameters:
 *    ev, eq, f - parameterization of absExp.
 *    env - the bindings for environment variables
 *    bindings - a list of bindings for quantified variables
 *    exp - the expression to evaluate
 *)
Fixpoint absEval (*{ev} {eq} {f}*) (env : id -> nat) (bindings : list (@Value unit)) (exp : @absExp) : (@Value unit) :=
    match exp with
    | AbsConstVal v => v
    | AbsVar v => NatValue (env v)
    | AbsFun id pl => basicEval id (map (absEval env bindings) pl)
    | AbsQVar n => nth n bindings NoValue
    end.

(************************************************************************************
 *
 * absRefExp
 *
 * An expression that references the heap
 *
 ************************************************************************************)

Inductive absRefExp (*{ev}
                    {eq : ev -> ev -> bool}
                    { f : id -> list (@Value ev) -> (@Value ev) }*) :=
   | AbsRefConstVal : (@Value unit) -> absRefExp
   | AbsRefVar : id -> absRefExp
   | AbsRefQVar : absVar -> absRefExp
   | AbsRefRef : absRefExp -> absRefExp
   | AbsRefFun : id -> list absRefExp -> absRefExp.

(* ************************************************************************************
 * Definition of expression evaluation--note how the "f" parameter of absExp is used to
 * define the semantics of absFun.
 *
 * Parameters:
 *    ev, eq, f - parameterization of absExp.
 *    env - the bindings for environment variables
 *    bindings - a list of bindings for quantified variables
 *    exp - the expression to evaluate
 *)
Fixpoint absRefEval (*{ev} {eq} {f}*) (env : id -> nat) (bindings : list (@Value unit)) (h : heap) (exp : @absRefExp): (@Value unit) :=
    match exp with
    | AbsRefConstVal v => v
    | AbsRefVar v => NatValue (env v)
    | AbsRefFun id pl => basicEval id (map (absRefEval env bindings h) pl)
    | AbsRefRef e => match (absRefEval env bindings h e) with
                     | NatValue v => match (h v) with
                                     | Some x => NatValue x
                                     | None => NoValue
                                     end
                     | _ => NoValue
                     end
    | AbsRefQVar n => nth n (rev bindings) NoValue
    end.


(************************************************************************************
 *
 * absState
 * This is the syntax for abstract states (or state assertions)
 *
 * Parameters:
 *    ev, eq, f - parameters passed on to absExp
 *    t - semantics for AbsLeaf
 *    ac - semantics for AbsAccumulate - AbsAccumulate is not defined in the system
 *         however, it is a place holder for future development.
 *
 ************************************************************************************)

Inductive absState (*{ev}
                   {eq : ev -> ev -> bool}
                   { f : id -> list (@Value ev) -> (@Value ev) }
                   { t : id -> list (@Value ev) -> heap -> Prop }
                   { ac : id -> (id -> nat) -> (list (@Value ev)) -> (list (@Value ev)) -> (@absExp ev eq f) -> @Value ev -> Prop }*) :=
   | AbsExists :  (absExp) -> absState -> absState
   | AbsExistsT : absState -> absState
   | AbsAll : (absExp) -> absState -> absState
   | AbsEach : (absExp) -> absState -> absState
   | AbsStar : absState -> absState -> absState
   | AbsOrStar : absState -> absState -> absState
   | AbsEmpty : absState
   | AbsAny : absState
   | AbsNone : absState
   | AbsLeaf : id -> (list absExp) -> absState
   | AbsAccumulate : id -> absExp -> absExp -> absExp -> absState
   | AbsMagicWand : absState -> absState -> absState
   | AbsUpdateVar : absState -> id -> absExp -> absState
   | AbsUpdateLoc : absState-> (absExp) -> (absExp) -> absState
   | AbsUpdateWithLoc : absState-> id -> (absExp) -> absState
   | AbsUpdState : absState-> absState -> absState -> absState
   | AbsClosure : absState -> (list absExp) -> absState.

Fixpoint beq_absExpList (*{ev} {eq} {f}*) (l1 : list absExp) (l2 : list absExp) :=
    match l1,l2 with
    | f1::r1,f2::r2 => if beq_absExp f1 f2 then beq_absExpList r1 r2 else false
    | nil,nil => true
    | _,_ => false
    end.

Fixpoint beq_absState (*{ev} {eq} {f} {t} {ac}*) (l : absState) (r : absState) :=
    match l,r with
    | AbsExists e1 s1,AbsExists e2 s2 => if beq_absExp e1 e2 then beq_absState s1 s2 else false
    | AbsExistsT s1, AbsExistsT s2 => beq_absState s1 s2
    | AbsAll e1 s1,AbsAll e2 s2 => if beq_absExp e1 e2 then beq_absState s1 s2 else false
    | AbsEach e1 s1,AbsEach e2 s2 => if beq_absExp e1 e2 then beq_absState s1 s2 else false
    | AbsStar l1 r1,AbsStar l2 r2 => if beq_absState l1 l2 then beq_absState r1 r2 else false
    | AbsOrStar l1 r1,AbsOrStar l2 r2 => if beq_absState l1 l2 then beq_absState r1 r2 else false
    | AbsMagicWand l1 r1,AbsMagicWand l2 r2 => if beq_absState l1 l2 then beq_absState r1 r2 else false
    | AbsEmpty, AbsEmpty => true
    | AbsNone, AbsNone => true
    | AbsAny, AbsAny => true
    | AbsAccumulate i1 ea1 ea2 ea3,AbsAccumulate i2 eb1 eb2 eb3 =>
             if beq_id i1 i2 then
                 (if beq_absExp ea1 eb1 then
                     (if beq_absExp ea2 eb2 then
                         beq_absExp ea3 eb3 else false) else false) else false
    | AbsUpdateVar s1 i1 e1,AbsUpdateVar s2 i2 e2 =>
             if beq_id i1 i2 then
                 (if beq_absState s1 s2 then beq_absExp e1 e2 else false)
             else false
    | AbsUpdateLoc s1 i1 e1,AbsUpdateLoc s2 i2 e2 =>
             if beq_absExp i1 i2 then
                 (if beq_absState s1 s2 then beq_absExp e1 e2 else false)
             else false
    | AbsUpdateWithLoc s1 i1 e1,AbsUpdateWithLoc s2 i2 e2 =>
             if beq_id i1 i2 then
                 (if beq_absState s1 s2 then beq_absExp e1 e2 else false)
             else false
    | AbsUpdState s1 i1 e1,AbsUpdState s2 i2 e2 =>
             if beq_absState i1 i2 then
                 (if beq_absState s1 s2 then beq_absState e1 e2 else false)
             else false
    | AbsLeaf i1 el1, AbsLeaf i2 el2 =>
             if beq_id i1 i2 then beq_absExpList el1 el2 else false
    (*| AbsClosure s1 el1,AbsClosure s2 el2 =>
             beq_absExpList el1 el2 else false*)
    | _,_ => false
    end.

Notation "x '**' y" := (AbsStar x y)
  (at level 100, right associativity).

Notation "x '*\/*' y" := (AbsOrStar x y)
  (at level 110, right associativity).

(* Auxiliary functions--either used in realizedState below or in theorems involving realizeState
   (in other files) *)

Fixpoint instantiateExp (*{ev:Type} {eq} {t}*) (e : absExp) (val:@Value unit) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar v => match v with
                  | 0 => AbsConstVal val
                  | S x => AbsQVar x
                  end
   | AbsFun id pl => AbsFun id (map (fun x => instantiateExp x val) pl)
   end.

Fixpoint instantiateState (*{ev} {eq} {f} {t} {ac}*) (s : absState) (val:@Value unit) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (instantiateState s1 val) (instantiateState s2 val))
    | AbsOrStar s1 s2 => (AbsOrStar (instantiateState s1 val) (instantiateState s2 val))
    | AbsExists e s => AbsExists (instantiateExp e val) (instantiateState s val)
    | AbsExistsT s => AbsExistsT (instantiateState s val)
    | AbsAll e s => AbsAll (instantiateExp e val) (instantiateState s val)
    | AbsEach e s => AbsEach (instantiateExp e val) (instantiateState s val)
    | AbsLeaf i el => AbsLeaf i (map (fun x => instantiateExp x val) el)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (instantiateExp e1 val) (instantiateExp e2 val) (instantiateExp e3 val)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsMagicWand s1 s2 => AbsMagicWand (instantiateState s1 val) (instantiateState s2 val)
    | AbsUpdateVar s v vall => AbsUpdateVar (instantiateState s val) v (instantiateExp vall val)
    | AbsUpdateWithLoc s v vall => AbsUpdateWithLoc (instantiateState s val) v (instantiateExp vall val)
    | AbsUpdateLoc s l vall => AbsUpdateLoc (instantiateState s val) (instantiateExp l val) (instantiateExp vall val)
    | AbsUpdState s11 s22 s33 => AbsUpdState (instantiateState s11 val) (instantiateState s22 val) (instantiateState s33 val)
    | AbsClosure s l => AbsClosure s (map (fun x => instantiateExp x val) l)
   end.

(* Some auxiliary definitions useful for realizeState *)
Inductive fold_compose : list state -> state -> Prop :=
  | FCNil : forall x, fold_compose nil (x,empty_heap)
  | FCCons : forall f r state rstate,
             fold_compose r rstate ->
             concreteCompose rstate f state ->
             fold_compose (f::r) state.

Inductive allFirsts {t1} {t2} : list t1 -> list (t1 * t2) -> Prop :=
  | AFNil : allFirsts nil nil
  | AFCons : forall fx fy r r', allFirsts r r' -> allFirsts (fx::r) ((fx,fy)::r').

Inductive allSeconds {t1} {t2} : list t1 -> list (t2 * t1) -> Prop :=
  | ASNil : allSeconds nil nil
  | ASCons : forall fx fy r r', allSeconds r r' -> allSeconds (fy::r) ((fx,fy)::r').

Inductive anyHeap : nat -> nat -> heap -> Prop :=
    | AnyHeapBase : forall start,
                    anyHeap start 0 (fun x => None)
    | AnyHeapNext : forall start next heap y,
                    anyHeap (S start) next heap ->
                    anyHeap start (S next) (fun x => if beq_nat x start then Some y else heap x).

Inductive Rcell : nat -> (list nat) -> heap -> nat -> Prop :=
  | RCellBase : forall l ll h,
                Rcell l ll h l
  | RCellNext : forall l ll index h n nn,
                mem_nat index ll=true ->
                h (n+index)=Some nn ->
                Rcell l ll h n ->
                Rcell l ll h nn.

Inductive mergeHeaps : (list heap) -> heap -> Prop :=
  | MHBase : mergeHeaps nil (fun x => None)
  | MHNext : forall f r h1 h2 h,
             mergeHeaps r h2 ->
             (forall x, h1 x=None \/ h2 x=None) ->
             h = (fun x => match h1 x with None => h2 x | Some x => Some x end) ->
             mergeHeaps (f::r) h.

Inductive heapWithIndexList {t} : (list nat) -> (list heap) -> (list (@Value t)) -> (list (nat * heap * (@Value t))) -> Prop :=
  | HWIBase : heapWithIndexList nil nil nil nil
  | HWINext : forall ir hr ihr br i h b,
              heapWithIndexList ir hr br ihr ->
              heapWithIndexList (i::ir) (h::hr) (b::br) ((i,h,b)::ihr).

Fixpoint findIndex {t} (n : nat) (h : heap) (l : list (nat * heap * (@Value t))) : @Value t :=
    match l with
    | nil => match h n with
             | Some x => NatValue x
             | None => NatValue 0
             end
    | ((nn,hh,v)::r) => if beq_nat n nn then v else findIndex n h r
    end.

Fixpoint buildList {t} (i : nat) (size : nat) (h : heap) (l : list (nat * heap * (@Value t))) : list (@Value t) :=
    match size with
    | 0 => nil
    | (S s) => (findIndex i h l)::(buildList (S i) s h l)
    end.

Inductive ihmem {t} : nat -> heap -> @Value t -> (list (nat * heap * (@Value t))) -> Prop :=
  | IHBase : forall n h v hl,
             ihmem n h v ((n,h,v)::hl)
  | IHNext : forall n h v f hl,
             ihmem n h v hl ->
             ihmem n h v (f::hl).

(*
 * Recursive definition for the TREE construct--used in the definition of basicState
 *
 * Parameters:
 *    #1 - root of tree
 *    #2 - size of each node in the tree
 *    #3 - list of offsets to fields for each node
 *    #4 - functional representation of the tree
 *    #5 - concrete heap (Must be exact heap for the tree)
 *)
Inductive Tree {t} : nat -> nat -> (list nat) -> (@Value t) -> heap -> Prop :=
  | TreeNext : forall root size indices heaps ihlist h0 h1 heap values vals,
            size > 0 ->
            anyHeap root size h0 ->
            heapWithIndexList indices heaps values ihlist ->
            not(root=0) ->
            (forall i h v x, ihmem i h v ihlist -> Some x=h0 (root+x) -> Tree x size indices v h) ->
            mergeHeaps heaps h1 ->
            (forall l, (h1 l=None \/ h0 l=None)) ->
            heap = (fun x => match h1 x with None =>  h0 x | Some x => Some x end) ->
            vals = buildList root size heap ihlist ->
            Tree root size indices (ListValue ((NatValue root)::vals)) heap
  | TreeBase : forall size index h,
            size > 0 ->
            (forall v, h v=None) ->
            Tree 0 size index (ListValue ((NatValue 0)::nil)) h.



(*
 * Rmember is a predicate used in AbsPredicate constructs to determine whether a nat
 * is in fact a pointer to the head of any of the nodes in the list or tree represented
 * by an RFun construct.
 *
 * Parameters:
 *    l - location to test
 *    tree - a tree (which is the same form as parameter #4 to tree above
 *
 * This definition is used in basicEval for the 'inTree' function
 *)

Theorem rootIsMember : forall t root size fields heap (v : @Value t),
    root <> 0 ->
    Tree root size fields v heap ->
    Rmember root v=true.
Proof. admit. Admitted.

Inductive strip_nat_values {t} : (list (@Value t)) -> (list nat) -> Prop :=
   | SNVNil : strip_nat_values nil nil
   | SNVCons : forall v a b,
               strip_nat_values a b ->
               strip_nat_values ((NatValue v)::a) (v::b).
(***************************************************************************
 *
 * basicState
 *
 * This is used to fill in the 't' parameter in absState.
 *
 ***************************************************************************)

Notation "'AbsPredicateId'" := (Id 101) (at level 1).
Notation "'AbsTreeId'" := (Id 102) (at level 1).
Notation "'AbsCellId'" := (Id 103) (at level 1).
Notation "'AbsArrayId'" := (Id 104) (at level 1).
Notation "'AbsPathId'" := (Id 105) (at level 1).

Inductive anyHeapv {t} : nat -> nat -> heap -> (list (@Value t)) -> Prop :=
    | AnyHeapvBase : forall start,
                     anyHeapv start 0 (fun x => None) nil
    | AnyHeapvNext : forall start next heap y r,
                     anyHeapv (S start) next heap r ->
                     anyHeapv start (S next) (fun x => if beq_nat x start then Some y else heap x)
                                    ((NatValue y)::r).

Inductive valueIndexList {t} : (list nat) -> (list (@Value t)) -> (list (nat * (@Value t))) -> Prop :=
  | VIBase : valueIndexList nil nil nil
  | VINext : forall ir br i b ibr,
              valueIndexList ir br ibr ->
              valueIndexList (i::ir) (b::br) ((i,b)::ibr).

Inductive imem {t} : nat -> @Value t -> (list (nat * (@Value t))) -> Prop :=
  | IBase : forall n v hl,
            imem n v ((n,v)::hl)
  | INext : forall n v f hl,
            imem n v hl ->
            imem n v (f::hl).

Inductive updateRec {t} : (list (nat * (@Value t))) -> nat -> list (@Value t) -> list (@Value t) -> Prop :=
  | UBase : forall n vl,
            updateRec vl n nil nil
  | UMem : forall n v vl or nr x,
           imem n v vl ->
           updateRec vl (n+1) or nr ->
           updateRec vl n (x::or) (v::nr)
  | UDef1 : forall n v vl or nr x,
            not(imem n v vl) ->
            updateRec vl (n+1) or nr ->
            updateRec vl n ((NatValue x)::or) ((NatValue x)::or)
  | UDef2 : forall n v vl or nr x rr,
            not(imem n v vl) ->
            updateRec vl (n+1) or nr ->
            updateRec vl n ((ListValue ((NatValue x)::rr))::or) ((NatValue x)::or).

Inductive Path {t} : nat -> nat -> (list nat) -> (@Value t) -> (@Value t) -> Prop :=
  | PathNext : forall root size indices baseData rec vals ivals rec2,
            size > 0 ->
            not(root=0) ->
            ((NatValue root)::rec) = findRecord root baseData ->
            valueIndexList indices vals ivals ->
            (forall i x v r, imem i v ivals -> ((ListValue ((NatValue x)::r))=nth i rec NoValue /\ Path x size indices baseData v)) ->
            updateRec ivals 0 rec rec2 ->
            Path root size indices baseData (ListValue (NatValue root::rec2))
  | PathBase : forall size l h,
            size > 0 ->
            Path 0 size l h (ListValue ((NatValue 0)::nil)).
Inductive basicState: id -> list (@Value unit) -> heap -> Prop :=
  | BTStatePredicate : forall e h,
                       e<>0 ->
                       (forall x, h x = None) ->
                       basicState AbsPredicateId ((NatValue e)::nil) h
  | BStateTree : forall r s f h ff tt,
                 Tree r s f tt h ->
                 strip_nat_values ff f ->
                 basicState AbsTreeId ((NatValue r)::tt::(NatValue s)::ff) h
  | BStatePath : forall r s f base path h ff,
                 Path r s f base path ->
                 strip_nat_values ff f ->
                 (forall x, h x = None) ->
                 basicState AbsPathId ((NatValue r)::base::path::(NatValue s)::ff) h
  | BStateArray : forall r s h vl,
                  anyHeapv r s h vl->
                  basicState AbsArrayId ((NatValue r)::(NatValue s)::(ListValue vl)::nil) h
  | BTStateCell : forall v l h,
                  h l = Some v ->
                  l<>0 ->
                  (forall x, x<>l -> h x=None) ->
                  basicState AbsCellId ((NatValue l)::(NatValue v)::nil) h.

(***************************************************************************
 *
 * basicAccumulate
 *
 * This is used to fill in the 'ac' parameter in absState.  For now, this is
 * a place holder.  There are no actual definitions.
 *
 ***************************************************************************)

Notation "'AbsSumId'" := (Id 201) (at level 1).

Inductive sumValues (*{t} {teq} {f}*) : (id -> nat) -> (list (@Value unit)) -> (list (@Value unit)) -> (absExp) -> (@Value unit) -> Prop :=
  | SumNil : forall b e env,
             sumValues env b nil e (NatValue 0)
  | SumCons : forall b e x ff r env y v,
              sumValues env b r e (NatValue x) ->
              absEval env (ff::b) e = NatValue v ->
              y = x+v ->
              sumValues env b (ff::r) e (NatValue y).

Inductive basicAccumulate (*{t} {teq} {f}*) : id -> (id -> nat) -> (list (@Value unit)) -> (list (@Value unit)) ->
                                          absExp ->
                                          (@Value unit) -> Prop :=
  | BASum : forall env b e l tt,
            sumValues env b l e tt ->
            basicAccumulate AbsSumId env b l e tt.

(******************************************************************************
 * realizeState - This function defines the semantics of abstract states with
 * respect to concrete states.
 *
 * Parameters:
 *     #1 - The abstract state
 *     #2 - A list of bindings for quantified variables--used for recursive
 *          calls which need to introduce quantified variables.  This parameter
 *          should just be set to nil when using realizeState from the outside
 *     #3 - The concrete state
 *
 ******************************************************************************)

Inductive realizeState (*{ev} {eq} {f} {t} {ac}*) : absState -> list (@Value unit) -> state -> Prop :=
  | RSCompose : forall s1 s2 as1 as2 s3 bindings,
                realizeState as1 bindings s1 ->
                realizeState as2 bindings s2 ->
                concreteCompose s1 s2 s3 ->
                realizeState (AbsStar as1 as2) bindings s3
  | RSOrComposeL : forall s1 as1 as2 bindings,
                   realizeState as1 bindings s1 ->
                   realizeState (AbsOrStar as1 as2) bindings s1
  | RSOrComposeR : forall s2 as1 as2 bindings,
                   realizeState as2 bindings s2 ->
                   realizeState (AbsOrStar as1 as2) bindings s2
  | RSExists : forall (s:state) (a:absState) e (v : @Value unit) rl bindings,
               absEval (env_p s) bindings e = v ->
               v = (ListValue rl) ->
               (exists x, In x rl /\
                       realizeState a (x::bindings) s) ->
               realizeState (AbsExists e a) bindings s
  | RSExistsU : forall s a bindings,
                 (exists x, realizeState a (x::bindings) s) ->
                 realizeState (AbsExistsT a) bindings s
  | RSAccumulate : forall s e1 e2 e3 vl v3 i bindings,
                    absEval (env_p s) bindings e1 = (ListValue vl) ->
                    absEval (env_p s) bindings e3 = v3 ->
                    basicAccumulate i (env_p s) bindings vl e2 v3 ->
                    realizeState (AbsAccumulate i e1 e2 e3) bindings s
  | RSAll : forall (s:state) (a:absState) e v rl bindings,
            absEval (env_p s) bindings e = v ->
            v = ListValue rl ->
            (forall x, In x rl ->
                       realizeState a (x::bindings) s) ->
            realizeState (AbsAll e a) bindings s
  | RSEach : forall (s:state) (a:absState) e v rl states bindings l,
             absEval (env_p s) bindings e = v ->
             v = ListValue rl ->
             allFirsts rl l ->
             allSeconds states l ->
             (forall x y, In (x,y) l -> realizeState a (x::bindings) y) ->
             fold_compose states s ->
             realizeState (AbsEach e a) bindings s
  | RSEmpty : forall s bindings,
              (forall x, snd s x=None) -> realizeState AbsEmpty bindings s
  | RSAny : forall s bindings, realizeState AbsAny bindings s
  | RSR : forall s el vl i bindings,
          map (absEval (env_p s) bindings) el = vl ->
          basicState i vl (snd s) ->
          realizeState (AbsLeaf i el) bindings s
  | RSMagicWand : forall s1 s2 as1 as2 s3 bindings,
                  realizeState as1 bindings s1 ->
                  realizeState as2 bindings s2 ->
                  concreteCompose s3 s2 s1 ->
                  realizeState (AbsMagicWand as1 as2) bindings s3
  | RSUpdateVar : forall s s1 as1 vv valaa valc bindings,
                  realizeState as1 bindings s1 ->
                  (NatValue valc) = absEval (env_p s) bindings valaa ->
                  (heap_p s) = (heap_p s1) ->
                  (override (env_p s) vv valc)= (env_p s1) ->
                  realizeState (AbsUpdateVar as1 vv valaa) bindings s
  | RSUpdateWithLoc : forall s s1 as1 vv valaa valc bindings vald,
                  realizeState as1 bindings s1 ->
                  (NatValue valc) = absEval (env_p s) bindings valaa ->
                  (heap_p s) = (heap_p s1) ->
                  (heap_p s) valc = Some vald ->
                  (override (env_p s) vv vald)= (env_p s1) ->
                  realizeState (AbsUpdateWithLoc as1 vv valaa) bindings s
  | RSUpdateLoc : forall s s1 as1 l ll valaa valc bindings qq,
                  realizeState as1 bindings s1 ->
                  heap_p s1 = qq ->
                  (NatValue ll) = absEval (env_p s) bindings l ->
                  (NatValue valc) = absEval (env_p s) bindings valaa ->
                  (heap_p s) = (fun fff => if beq_nat fff ll then Some valc else (heap_p s1) fff) ->
                  (env_p s) = (env_p s1) ->
                  realizeState (AbsUpdateLoc as1 l valaa) bindings s
  | RSUpdState : forall s1 s2 s3 as1 as2 as3 s4 s5 bindings,
                 realizeState as1 bindings s1 ->
                 realizeState as2 bindings s2 ->
                 realizeState as3 bindings s3 ->
                 concreteCompose s4 s2 s1 ->
                 concreteCompose s4 s3 s5 ->
                 realizeState (AbsUpdState as1 as2 as3) bindings s5
  | RSClosure : forall e h as1 bindings el b,
                 map (absEval e bindings) el = b ->
                 realizeState as1 b (empty_env,h) ->
                 realizeState (AbsClosure as1 el) bindings (e,h).

Theorem emptyConcreteCompose : forall e,
    concreteCompose (e,empty_heap) (e,empty_heap) (e,empty_heap).
Proof.
    intros. unfold concreteCompose. crunch. left. unfold empty_heap. reflexivity.
Qed. 

(******************************************************************************
 * This section contains a whole bunch of auxiliary definitions which are useful
 * in defining operators or tactics involving absState.  They are used in many
 * other files.
 ******************************************************************************)

(*Fixpoint pushAbsVar (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar vv => AbsVar vv
   | AbsQVar v => AbsQVar (S v)
   | AbsFun i el => AbsFun i (map pushAbsVar el)
   end. 

Fixpoint pushAbsVarState (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsOrStar s1 s2 => (AbsOrStar (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsExists e s => AbsExists (pushAbsVar e) (pushAbsVarState s)
    | AbsExistsT s => AbsExistsT (pushAbsVarState s)
    | AbsAll e s => AbsAll (pushAbsVar e) (pushAbsVarState s)
    | AbsEach e s => AbsEach (pushAbsVar e) (pushAbsVarState s)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (pushAbsVar e1) (pushAbsVar e2) (pushAbsVar e3)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i el => AbsLeaf i (map pushAbsVar el)
    | AbsMagicWand s1 s2 => (AbsMagicWand (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsUpdateWithLoc s v vall => (AbsUpdateWithLoc (pushAbsVarState s) v (pushAbsVar vall))
    | AbsUpdateVar s v vall => (AbsUpdateVar (pushAbsVarState s) v (pushAbsVar vall))
    | AbsUpdateLoc s v vall => (AbsUpdateLoc (pushAbsVarState s) (pushAbsVar v) (pushAbsVar vall))
    | AbsUpdState s1 s2 s3 => (AbsUpdState (pushAbsVarState s1) (pushAbsVarState s2) (pushAbsVarState s3))
    | AbsClosure s el => (AbsClosure s (map pushAbsVar el))
   end.*)

Fixpoint quantifyAbsVar (e : absExp) (vn : nat) (n : nat) (v:id) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar vv => if beq_id vv v then AbsQVar vn else AbsVar vv
   | AbsQVar vv => if ble_nat n vv then AbsQVar (vv+1) else AbsQVar vv
   | AbsFun i el => AbsFun i (map (fun x => quantifyAbsVar x vn n v) el)
   end.

Fixpoint quantifyAbsVarState (s : absState) (vn : nat) (n:nat) (v:id) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (quantifyAbsVarState s1 vn n v) (quantifyAbsVarState s2 vn n v))
    | AbsOrStar s1 s2 => (AbsOrStar (quantifyAbsVarState s1 vn n v) (quantifyAbsVarState s2 vn n v))
    | AbsExists e s => AbsExists (quantifyAbsVar e vn n v) (quantifyAbsVarState s (S vn) (S n) v)
    | AbsExistsT s => AbsExistsT (quantifyAbsVarState s (S vn) (S n) v)
    | AbsAll e s => AbsAll (quantifyAbsVar e vn n v) (quantifyAbsVarState s (S vn) (S n) v)
    | AbsEach e s => AbsEach (quantifyAbsVar e vn n v) (quantifyAbsVarState s (S vn) (S n) v)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (quantifyAbsVar e1 vn n v) (quantifyAbsVar e2 vn n v) (quantifyAbsVar e3 vn n v)
    | AbsLeaf i el => AbsLeaf i (map (fun x => quantifyAbsVar x vn n v) el)
    | AbsMagicWand s1 s2 => (AbsMagicWand (quantifyAbsVarState s1 vn n v) (quantifyAbsVarState s2 vn n v))
    | AbsUpdateVar s vv vall => (AbsUpdateVar (quantifyAbsVarState s vn n v) vv (quantifyAbsVar vall vn n v))
    | AbsUpdateWithLoc s vv vall => (AbsUpdateWithLoc (quantifyAbsVarState s vn n v) vv (quantifyAbsVar vall vn n v))
    | AbsUpdateLoc s l vall => (AbsUpdateLoc (quantifyAbsVarState s vn n v) (quantifyAbsVar l vn n v) (quantifyAbsVar vall vn n v))
    | AbsUpdState s1 s2 s3 => (AbsUpdState (quantifyAbsVarState s1 vn n v) (quantifyAbsVarState s2 vn n v) (quantifyAbsVarState s3 vn n v))
    | AbsClosure s el => (AbsClosure s (map (fun x => quantifyAbsVar x vn n v) el))
   end.

Fixpoint convertAbsValue {ev} {ev'} (m : ev -> ev') (v : @Value ev) : @Value ev' :=
   match v with
   | NatValue v => NatValue v
   | ListValue l => ListValue (map (convertAbsValue m) l)
   | NoValue => NoValue
   | OtherValue v => OtherValue (m v)
   end.

Fixpoint convertAbsExp (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun id pl => AbsFun id pl
   end.


Fixpoint subst (e : absExp) (n: nat) (val:absExp) : absExp :=
   match e with
   | AbsConstVal x => AbsConstVal x
   | AbsVar v => AbsVar v
   | AbsQVar v => if beq_nat v n then val else (AbsQVar v)
   | AbsFun i l => AbsFun i (map (fun x => subst x n val) l)
   end.

Fixpoint substState (s : absState) (n : nat) (val:absExp) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (substState s1 n val) (substState s2 n val))
    | AbsOrStar s1 s2 => (AbsOrStar (substState s1 n val) (substState s2 n val))
    | AbsExistsT s => AbsExistsT (substState s (S n) val)
    | AbsExists e s => AbsExists (subst e n val) (substState s (S n) val)
    | AbsAll e s => AbsAll (subst e n val) (substState s (S n) val)
    | AbsEach e s => AbsEach (subst e n val) (substState s (S n) val)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map (fun x => subst x n val) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (subst e1 n val) (subst e2 n val) (subst e3 n val)
    | AbsMagicWand s1 s2 => AbsMagicWand (substState s1 n val) (substState s2 n val)
    | AbsUpdateVar s v vall => AbsUpdateVar (substState s n val) v (subst vall n val)
    | AbsUpdateWithLoc s v vall => AbsUpdateWithLoc (substState s n val) v (subst vall n val)
    | AbsUpdateLoc s l vall => AbsUpdateLoc (substState s n val) (subst l n val) (subst vall n val)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (substState s1 n val) (substState s2 n val) (substState s3 n val))
    | AbsClosure s l => AbsClosure s (map (fun x => subst x n val) l)
   end.

Fixpoint addExpVar (v : nat) (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if ble_nat v vv then AbsQVar (vv+1) else AbsQVar vv
   | AbsFun i l => AbsFun i (map (addExpVar v) l)
   end.

Fixpoint addStateVar (n : nat) (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (addStateVar n s1) (addStateVar n s2))
    | AbsOrStar s1 s2 => (AbsOrStar (addStateVar n s1) (addStateVar n s2))
    | AbsExistsT s => AbsExistsT (addStateVar (S n) s)
    | AbsExists e s => AbsExists (addExpVar n e) (addStateVar (S n) s)
    | AbsAll e s => AbsAll (addExpVar n e) (addStateVar (S n) s)
    | AbsEach e s => AbsEach (addExpVar n e) (addStateVar (S n) s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map (addExpVar n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (addExpVar n e1) (addExpVar n e2) (addExpVar n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (addStateVar n s1) (addStateVar n s2)
    | AbsUpdateVar s v vall => AbsUpdateVar (addStateVar n s) v (addExpVar n vall)
    | AbsUpdateWithLoc s v vall => AbsUpdateWithLoc (addStateVar n s) v (addExpVar n vall)
    | AbsUpdateLoc s v vall => AbsUpdateLoc (addStateVar n s) (addExpVar n v) (addExpVar n vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (addStateVar n s1) (addStateVar n s2) (addStateVar n s3))
    | AbsClosure s l => AbsClosure s (map (addExpVar n) l)
   end.

Fixpoint substVar (e : absExp) (n: id) (val:absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => if beq_id v n then val else AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun i l => AbsFun i (map (fun x => substVar x n val) l)
   end.

Fixpoint substVarState (s : absState) (n : id) (val:absExp) : option absState :=
   match s with
    | AbsStar s1 s2 => match substVarState s1 n val,substVarState s2 n val with
                       | Some a,Some b => Some (AbsStar a b)
                       | _,_ => None
                       end
    | AbsOrStar s1 s2 => match substVarState s1 n val,substVarState s2 n val with
                         | Some a,Some b => Some (AbsOrStar a b)
                         | _,_ => None
                         end
    | AbsExistsT s => match substVarState s n (addExpVar 0 val) with
                      | Some x => Some (AbsExistsT x)
                      | _ => None
                      end
    | AbsExists e s => match substVarState s n (addExpVar 0 val) with
                       | Some x => Some (AbsExists (substVar e n val) x)
                       | None => None
                       end
    | AbsAll e s => match substVarState s n (addExpVar 0 val) with
                    | Some x => Some (AbsAll (substVar e n val) x)
                    | None => None
                    end
    | AbsEach e s => match substVarState s n (addExpVar 0 val) with
                     | Some x => Some (AbsEach (substVar e n val) x)
                     | None => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsAny => Some AbsAny
    | AbsNone => Some AbsNone
    | AbsLeaf i l => Some (AbsLeaf i (map (fun x => substVar x n val) l))
    | AbsAccumulate id e1 e2 e3 => Some (AbsAccumulate id (substVar e1 n val) (substVar e2 n val) (substVar e3 n val))
    | AbsMagicWand s1 s2 => match substVarState s1 n val,substVarState s2 n val with
                            | Some a,Some b => Some (AbsMagicWand a b)
                            | _,_ => None
                            end
    | AbsUpdateVar s v vall => if beq_id v n then None
                               else match substVarState s n val with
                                    | Some x => Some (AbsUpdateVar x v (substVar vall n val))
                                    | _ => None
                                    end
    | AbsUpdateWithLoc s v vall => if beq_id v n then None
                                   else match substVarState s n val with
                                        | Some x => Some (AbsUpdateWithLoc x v (substVar vall n val))
                                        | _ => None
                                        end
    | AbsUpdateLoc s v vall => match (substVarState s n val),(substVar v n val),(substVar vall n val) with
                               | Some a,b,c => Some (AbsUpdateLoc a b c)
                               | _,_,_ => None
                               end
    | AbsUpdState s1 s2 s3 =>  match (substVarState s1 n val),(substVarState s2 n val),(substVarState s3 n val) with
                               | Some a,Some b,Some c => Some (AbsUpdState a b c)
                               | _,_,_ => None
                               end
    | AbsClosure s l => Some (AbsClosure s (map (fun x => substVar x n val) l))
   end.

Fixpoint hasVnExp (e : absExp) (v : absVar) : bool :=
   match e with
   | AbsConstVal v => false
   | AbsVar vv => false
   | AbsQVar vv => beq_nat vv v
   | AbsFun i l => (fix go l := match l with
                               | (f::r) => if hasVnExp f v then true else go r
                               | nil => false
                               end) l
   end.

Fixpoint hasVnState (s : absState) (v : absVar) : bool :=
    match s with
    | AbsStar s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsOrStar s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsExistsT s => hasVnState s (S v)
    | AbsExists e s => if hasVnExp e v then true else hasVnState s (S v)
    | AbsAll e s => if hasVnExp e v then true else hasVnState s (S v)
    | AbsEach e s => if hasVnExp e v then true else hasVnState s (S v)
    | AbsLeaf i l => (fix go l := match l with
                               | (f::r) => if hasVnExp f v then true else go r
                               | nil => false
                               end) l
    | AbsAccumulate id e1 e2 e3 => if hasVnExp e1 v then true else
                                   if hasVnExp e2 v then true else
                                   if hasVnExp e3 v then true else false
    | AbsMagicWand s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsUpdateVar s vv vall => if (hasVnState s v:bool) then true else hasVnExp vall v
    | AbsUpdateWithLoc s vv vall => if (hasVnState s v:bool) then true else hasVnExp vall v
    | AbsUpdateLoc s l vall => if (hasVnState s v) then true
                                else (if hasVnExp vall v then true else hasVnExp l v)
    | AbsUpdState s1 s2 s3 => if (hasVnState s1 v:bool) then true else
                              if (hasVnState s2 v:bool) then true else
                              hasVnState s3 v
    | AbsClosure s l => (fix go l := match l with
                               | (f::r) => if hasVnExp f v then true else go r
                               | nil => false
                               end) l
    | _ => false
    end.

Fixpoint hasVarExp (e : absExp) (v : id) : bool :=
   match e with
   | AbsConstVal v => false
   | AbsVar vv => beq_id vv v
   | AbsQVar vv => false
   | AbsFun i l => (fix go l := match l with
                               | (f::r) => if hasVarExp f v then true else go r
                               | nil => false
                               end) l
   end.

Fixpoint hasVarState (s : absState) (v : id) : bool :=
    match s with
    | AbsStar s1 s2 => if (hasVarState s1 v:bool) then true else hasVarState s2 v
    | AbsOrStar s1 s2 => if (hasVarState s1 v:bool) then true else hasVarState s2 v
    | AbsExistsT s => hasVarState s v
    | AbsExists e s => if hasVarExp e v then true else hasVarState s v
    | AbsAll e s => if hasVarExp e v then true else hasVarState s v
    | AbsEach e s => if hasVarExp e v then true else hasVarState s v
    | AbsLeaf i l => (fix go l := match l with
                               | (f::r) => if hasVarExp f v then true else go r
                               | nil => false
                               end) l
    | AbsAccumulate id e1 e2 e3 => if hasVarExp e1 v then true else
                                   if hasVarExp e2 v then true else
                                   if hasVarExp e3 v then true else false
    | AbsMagicWand s1 s2 => if (hasVarState s1 v:bool) then true else hasVarState s2 v
    | AbsUpdateVar s vv vall => if (hasVarState s v:bool) then true else hasVarExp vall v
    | AbsUpdateWithLoc s vv vall => if (hasVarState s v:bool) then true else hasVarExp vall v
    | AbsUpdateLoc s l vall => if (hasVarState s v:bool) then true else if hasVarExp l v then true else hasVarExp vall v
    | AbsUpdState s1 s2 s3 => if (hasVarState s1 v:bool) then true else
                              if (hasVarState s2 v:bool) then true else
                              hasVarState s3 v
    | AbsClosure s l => (fix go l := match l with
                               | (f::r) => if hasVarExp f v then true else go r
                               | nil => false
                               end) l
    | _ => false
    end.

Fixpoint shareVarExpState (e : absExp) (s : absState) : bool :=
   match e with
   | AbsConstVal v => false
   | AbsVar vv => hasVarState s vv
   | AbsQVar vv => false
   | AbsFun i l => (fix go l := match l with
                               | (f::r) => if shareVarExpState f s then true else go r
                               | nil => false
                               end) l
   end.

Fixpoint shareVarState (s : absState) (v : absState) : bool :=
    match s with
    | AbsStar s1 s2 => if (shareVarState s1 v:bool) then true else shareVarState s2 v
    | AbsOrStar s1 s2 => if (shareVarState s1 v:bool) then true else shareVarState s2 v
    | AbsExistsT s => shareVarState s v
    | AbsExists e s => if shareVarExpState e v then true else shareVarState s v
    | AbsAll e s => if shareVarExpState e v then true else shareVarState s v
    | AbsEach e s => if shareVarExpState e v then true else shareVarState s v
    | AbsLeaf i l => (fix go l := match l with
                               | (f::r) => if shareVarExpState f v then true else go r
                               | nil => false
                               end) l
    | AbsAccumulate id e1 e2 e3 => if shareVarExpState e1 v then true else
                                   if shareVarExpState e2 v then true else
                                   if shareVarExpState e3 v then true else false
    | AbsMagicWand s1 s2 => if (shareVarState s1 v:bool) then true else shareVarState s2 v
    | AbsUpdateVar s vv vall => if (shareVarState s v:bool) then true else shareVarExpState vall v
    | AbsUpdateWithLoc s vv vall => if (shareVarState s v:bool) then true else shareVarExpState vall v
    | AbsUpdateLoc s l vall => if (shareVarState s v:bool) then true else if shareVarExpState l v then true else shareVarExpState vall v
    | AbsUpdState s1 s2 s3 => if (shareVarState s1 v:bool) then true else
                              if (shareVarState s2 v:bool) then true else
                              shareVarState s3 v
    | AbsClosure s l => (fix go l := match l with
                               | (f::r) => if shareVarExpState f v then true else go r
                               | nil => false
                               end) l
    | _ => false
    end.
Inductive an_empty_state : absState -> Prop :=
  | ESCompose : forall p1 p2,
                an_empty_state p1 ->
                an_empty_state p2 ->
                an_empty_state (p1 ** p2)
  | ESOrCompose : forall p1 p2,
                an_empty_state p1 ->
                an_empty_state p2 ->
                an_empty_state (p1 *\/* p2)
  | ESEmpty : an_empty_state AbsEmpty.

Ltac solveEmptyState :=
    solve [(eapply ESCompose;solveEmptyState) | (eapply ESOrCompose;solveEmptyState) | eapply ESEmpty].

Fixpoint removeExpVar (v : nat) (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if ble_nat vv v then AbsQVar vv else AbsQVar (vv-1)
   | AbsFun i l => AbsFun i (map (removeExpVar v) l)
   end.

Fixpoint removeStateVar (n : nat) (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeStateVar n s1) (removeStateVar n s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeStateVar n s1) (removeStateVar n s2))
    | AbsExistsT s => AbsExistsT (removeStateVar (S n) s)
    | AbsExists e s => AbsExists (removeExpVar n e) (removeStateVar (S n) s)
    | AbsAll e s => AbsAll (removeExpVar n e) (removeStateVar (S n) s)
    | AbsEach e s => AbsEach (removeExpVar n e) (removeStateVar (S n) s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map (removeExpVar n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (removeExpVar n e1) (removeExpVar n e2) (removeExpVar n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeStateVar n s1) (removeStateVar n s2)
    | AbsUpdateVar s v vall => AbsUpdateVar (removeStateVar n s) v (removeExpVar n vall)
    | AbsUpdateWithLoc s v vall => AbsUpdateWithLoc (removeStateVar n s) v (removeExpVar n vall)
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (removeStateVar n s) (removeExpVar n vv) (removeExpVar n vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (removeStateVar n s1) (removeStateVar n s2) (removeStateVar n s3))
    | AbsClosure s l => AbsClosure s (map (removeExpVar n) l)
   end.

(*Fixpoint N (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => AbsQVar (S vv)
   | AbsFun i l => AbsFun i (map N l)
   end.

Fixpoint NS (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (NS s1) (NS s2))
    | AbsOrStar s1 s2 => (AbsOrStar (NS s1) (NS s2))
    | AbsExistsT s => AbsExistsT (NS s)
    | AbsExists e s => AbsExists (N e) (NS s)
    | AbsAll e s => AbsAll (N e) (NS s)
    | AbsEach e s => AbsEach (N e) (NS s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map N l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (N e1) (N e2) (N e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (NS s1) (NS s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (NS s) vv (N vall)
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (NS s) vv (N vall)
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (NS s) (N vv) (N vall)
    | AbsUpdState s1 s2 s3 =>  AbsUpdState (NS s1) (NS s2) (NS s3)
    | AbsClosure s l => AbsClosure s (map N l)
   end.*)

Fixpoint replaceExpVar (v : nat) (rr : absExp) (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if beq_nat v vv then rr else AbsQVar vv
   | AbsFun i l => AbsFun i (map (replaceExpVar v rr) l)
   end.

Fixpoint replaceStateVar (n : nat) (rr : absExp) (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceStateVar n rr s1) (replaceStateVar n rr s2))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceStateVar n rr s1) (replaceStateVar n rr s2))
    | AbsExistsT s => AbsExistsT (replaceStateVar (S n) (addExpVar 0 rr) s)
    | AbsExists e s => AbsExists (replaceExpVar n rr e) (replaceStateVar (S n) (addExpVar 0 rr) s)
    | AbsAll e s => AbsAll (replaceExpVar n rr e) (replaceStateVar (S n) (addExpVar 0 rr) s)
    | AbsEach e s => AbsEach (replaceExpVar n rr e) (replaceStateVar (S n) (addExpVar 0 rr) s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map (replaceExpVar n rr) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExpVar n rr e1) (replaceExpVar n rr e2) (replaceExpVar n rr e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceStateVar n rr s1) (replaceStateVar n rr s2)
    | AbsUpdateVar s v vall => AbsUpdateVar (replaceStateVar n rr s) v (replaceExpVar n rr vall)
    | AbsUpdateWithLoc s v vall => AbsUpdateWithLoc (replaceStateVar n rr s) v (replaceExpVar n rr vall)
    | AbsUpdateLoc s v vall => AbsUpdateLoc (replaceStateVar n rr s) (replaceExpVar n rr v) (replaceExpVar n rr vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (replaceStateVar n rr s1) (replaceStateVar n rr s2) (replaceStateVar n rr s3))
    | AbsClosure s l => AbsClosure s (map (replaceExpVar n rr) l)
   end.

Fixpoint replaceExpExp (v : absExp) (rr : absExp) (e : absExp) : absExp :=
   if beq_absExp v e then rr else 
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => AbsQVar vv
   | AbsFun i l => AbsFun i (map (replaceExpExp v rr) l)
   end.

Fixpoint replaceStateExp (v : absExp) (rr : absExp) (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceStateExp v rr s1) (replaceStateExp v rr s2))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceStateExp v rr s1) (replaceStateExp v rr s2))
    | AbsExistsT s => AbsExistsT (replaceStateExp v rr s)
    | AbsExists e s => AbsExists (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsAll e s => AbsAll (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsEach e s => AbsEach (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map (replaceExpExp v rr) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExpExp v rr e1) (replaceExpExp v rr e2) (replaceExpExp v rr e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceStateExp v rr s1) (replaceStateExp v rr s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (replaceStateExp v rr s) vv (replaceExpExp v rr vall)
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (replaceStateExp v rr s) vv (replaceExpExp v rr vall)
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (replaceStateExp v rr s) (replaceExpExp v rr vv) (replaceExpExp v rr vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (replaceStateExp v rr s1) (replaceStateExp v rr s2) (replaceStateExp v rr s3))
    | AbsClosure s l => AbsClosure s (map (replaceExpExp v rr) l)
   end.

(*Fixpoint P (e : absExp) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar 0 => AbsQVar 0
   | AbsQVar (S vv) => AbsQVar vv
   | AbsFun i l => AbsFun i (map P l)
   end.

Fixpoint PS (s : absState) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (PS s1) (PS s2))
    | AbsOrStar s1 s2 => (AbsOrStar (PS s1) (PS s2))
    | AbsExistsT s => AbsExistsT (PS s)
    | AbsExists e s => AbsExists (P e) (PS s)
    | AbsAll e s => AbsAll (P e) (PS s)
    | AbsEach e s => AbsEach (P e) (PS s)
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i l => AbsLeaf i (map P l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (P e1) (P e2) (P e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (PS s1) (PS s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (PS s) vv (P vall)
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (PS s) vv (P vall)
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (PS s) (P vv) (P vall)
    | AbsUpdState s1 s2 s3 =>  AbsUpdState (PS s1) (PS s2) (PS s3)
    | AbsClosure s l => AbsClosure s (map P l)
   end.*)

(***************************************************************************************
 *
 * supportsFunctionality
 *
 * This function is used to parameterize many of the proofs in Pedantic
 * It is used to verify that one set of absState parameters (ev, eq, f, t and ac)
 * is a subset of another parameterization (ev',eq',f',t' and ac'). t_count, f_count, ac_count,
 * t_count', f_count' and ac_count' are used to specify the # of functions defined.
 *
 * Consider the proof of assign in AbsExecute.v.  This proof is dependent on the fact that
 * the AbsState type is parameterized with 'f' and 't' parameters that implement the
 * many of the operators defined basicEval and basicState (from AbsStateInstance.v).
 * We do not want to directly parameterize the AbsState type in the assign proof with
 * basicEval and basicState.  This would not allow the user to replace these functions without
 * redoing the proof.  Instead, the proof contains as one of its hypotheses, a predicate
 * of the form:
 *     supportsBasicFunctionality ...
 * (which is derived from supportsFunctionality below).  This predicate asserts that what ever
 * 'f' and 't' parameters are filled into the AbsState type will at the very least support
 * the operators defined inside of basicEval and basicState.
 *
 ***************************************************************************************)

(*Definition supportsFunctionality ev eq (f : id -> list (@Value ev) -> (@Value ev)) (f_count : nat)
                                 (t : id -> list (@Value ev) -> heap -> Prop) (t_count : nat)
                                 (ac : id -> (id -> nat) -> (list (@Value ev)) -> (list (@Value ev)) -> (@absExp ev eq f) -> @Value ev -> Prop)
                                 (ac_count : nat)
                                 ev' eq' (f' : id -> list (@Value ev') -> (@Value ev')) (t' : id -> list (@Value ev') -> heap -> Prop)
                                 (ac' : id -> (id -> nat) -> (list (@Value ev')) -> (list (@Value ev')) -> (@absExp ev' eq' f') -> @Value ev' -> Prop)
                                 (mfun : ev' -> ev) (rfun : ev -> ev') :=
    (forall (i : nat) (vl : list (@Value ev)) mrv, i < f_count -> map (convertAbsValue mfun) mrv = vl -> f' (Id i) mrv = convertAbsValue rfun (f (Id i) vl)) /\
    (forall (i : nat) (vl : list (@Value ev')) mrv, i < f_count -> map (convertAbsValue rfun) mrv = vl -> f (Id i) mrv = convertAbsValue mfun (f' (Id i) vl)) /\
    (forall (i : nat) (vl : list (@Value ev)) (h : heap) mr, t (Id i) vl h -> mr = (map (convertAbsValue rfun) vl) -> i < t_count -> t' (Id i) mr h) /\
    (forall (i : nat) (vl : list (@Value ev')) (h : heap) mr, t' (Id i) vl h -> mr = (map (convertAbsValue mfun) vl) -> i < t_count -> t (Id i) mr h) /\
    (forall (i : nat) (vl : list (@Value ev)) (env : id -> nat) (b : list (@Value ev)) (e : @absExp ev eq f) (v : @Value ev),
        ac (Id i) env b vl e v -> i < ac_count -> ac' (Id i) env (map (convertAbsValue rfun) b) (map (convertAbsValue rfun) vl) (convertAbsExp rfun e) (convertAbsValue rfun v)) /\
    (forall (i : nat) (env : id -> nat) (b : list (@Value ev')) (vl : list (@Value ev')) (e : @absExp ev' eq' f') (v : @Value ev'),
        ac' (Id i) env b vl e v -> i < ac_count -> ac (Id i) env (map (convertAbsValue mfun) b) (map (convertAbsValue mfun) vl) (convertAbsExp mfun e) (convertAbsValue mfun v)).*)

(***************************************************************************************
 *
 * Some useful properties--associativity, communitivity of AbsStar as well as
 * identity (AbsStar AbsEmpty ...) or (AbsStar ... AbsEmpty)
 *
 ***************************************************************************************)

Theorem composeEmpty1 : forall s1 s2,  (forall x, s2 x = None) -> compose_heaps s1 s2=s1.
Proof.
    intros. unfold compose_heaps. extensionality x. destruct (s1 x). reflexivity. apply H.
Qed.

Theorem composeEmpty2 : forall s1 s2,  (forall x, s1 x = None) -> compose_heaps s1 s2=s2.
Proof.
    intros. unfold compose_heaps. extensionality x. rewrite H. reflexivity.
Qed.

(*Theorem composeEmptyRight :
    forall (s : absState ev eq f t ac) state bindings,
    realizeState (AbsStar s AbsEmpty) bindings state <-> realizeState s bindings state.
Proof.
    crunch. inversion H. subst. clear H. inversion H3. subst. clear H3.
    crunch. unfold concreteCompose in H6. crunch. erewrite composeEmpty1 in H5.
    destruct s1. destruct state. crunch. crunch.

    eapply RSCompose with (s2 := (fst state,empty_heap)). crunch.
    eapply RSEmpty. crunch. unfold concreteCompose. crunch. right. unfold empty_heap. crunch.
    rewrite composeEmpty1. crunch. unfold empty_heap. crunch.
Qed.

Theorem composeEmptyLeft {ev} {eq} {f} {t} {ac} :
    forall (s : @absState ev eq f t ac) state bindings,
    realizeState (AbsStar AbsEmpty s) bindings state <-> realizeState s bindings state.
Proof.
    crunch. inversion H. subst. clear H. inversion H2. subst. clear H2.
    unfold concreteCompose in H6. crunch. erewrite composeEmpty2 in H5.
    destruct s2. destruct state. crunch. crunch.

    eapply RSCompose with (s1 := (fst state,empty_heap)). eapply RSEmpty.
    unfold empty_heap. crunch. crunch.
    unfold concreteCompose. crunch. left. unfold empty_heap. crunch.
Qed.

Theorem composeHeapsCommuntative : forall h0 h1, (forall x, h0 x = None \/ h1 x = None) -> compose_heaps h0 h1 = compose_heaps h1 h0.
Proof.
    crunch. unfold compose_heaps. extensionality x. crunch.
    assert (h0 x = None \/ h1 x = None). crunch. caseAnalysis.
Qed.

Theorem composeCommuntative {ev} {eq} {f} {t} {ac} :
    forall (s1 : @absState ev eq f t ac) s2 state bindings,
    realizeState (AbsStar s1 s2) bindings state -> realizeState (AbsStar s2 s1) bindings state.
Proof.
    crunch.
    inversion H. subst. clear H. destruct s0. destruct s3. destruct state.
    inversion H6. subst. clear H6. crunch.
    eapply RSCompose. crunch. crunch.
    unfold concreteCompose. crunch. crunch. apply or_comm. crunch. rewrite composeHeapsCommuntative.
    crunch. intros. apply or_comm. crunch.
Qed.

Theorem composeNone1 : forall h1 h2 x, compose_heaps h1 h2 x = None -> h1 x = None.
Proof.

    crunch. unfold compose_heaps in H. destruct (h1 x). crunch. crunch.
Qed.

Theorem composeNone2 : forall h1 h2 x, compose_heaps h1 h2 x = None -> h2 x = None.
Proof.
    crunch. unfold compose_heaps in H. destruct (h1 x). crunch. crunch.
Qed.

Theorem composeAssoc {ev} {eq} {f} {t} {ac} :
    forall (s1 : @absState ev eq f t ac) s2 s3 state bindings,
    realizeState (AbsStar (AbsStar s1 s2) s3) bindings state <-> realizeState (AbsStar s1 (AbsStar s2 s3)) bindings state.
Proof.
    crunch.

    inversion H. subst. clear H. inversion H2. subst. clear H2. destruct s4. destruct s5.
    destruct s6. destruct s0. inversion H8. subst. clear H8. crunch.
    unfold concreteCompose in H6. crunch.

    eapply RSCompose. crunch. eapply RSCompose. crunch. crunch.
    unfold concreteCompose. instantiate (1 := (_,_)). split. 2:split. 3:split. 4:crunch.
    crunch. crunch. crunch.
    assert (compose_heaps h0 h1 v = None \/ h v = None). crunch.
    assert (h0 v = None \/ h1 v = None). crunch.
    inversion H6. unfold compose_heaps in H5. crunch. crunch. crunch.
    unfold concreteCompose. crunch.
    assert (compose_heaps h0 h1 v = None \/ h v = None). crunch.
    assert (h0 v = None \/ h1 v = None). crunch.
    inversion H6. crunch. unfold compose_heaps in H5. rewrite H7 in H5. remember (h0 v). destruct o.
    inversion H5. crunch. unfold compose_heaps. rewrite H7. crunch. crunch.
    rewrite <- H2. unfold compose_heaps. crunch.
    caseAnalysis.

    inversion H. subst. clear H. inversion H3. subst. clear H3. destruct s4. destruct s5.
    destruct s6. destruct s0. unfold concreteCompose in H8. crunch. unfold concreteCompose in H6.
    crunch.

    eapply RSCompose. eapply RSCompose.
    crunch. crunch. crunch.
    unfold concreteCompose. instantiate (1 := (_,_)). split. 2:split. 3:split. 4:crunch.
    4:crunch.
    crunch. crunch. crunch.
    assert (h0 v = None \/ h1 v = None). crunch.
    assert (h2 v = None \/ compose_heaps h0 h1 v = None). crunch.
    caseAnalysis. unfold compose_heaps in H7. caseAnalysis.
    unfold concreteCompose. crunch.
    assert (h0 v = None \/ h1 v = None). crunch.
    assert (h2 v = None \/ compose_heaps h0 h1 v = None). crunch.
    caseAnalysis.
    unfold compose_heaps. crunch.
    unfold compose_heaps. unfold compose_heaps in H7. crunch.
    crunch. rewrite <- H3. unfold compose_heaps. crunch. caseAnalysis.
Qed.*)

Fixpoint subVarList vv (l : list absExp):=
    match l with
    | (ff::r) => match vv with
                | 0 => ff
                | S n => subVarList n r
                end
    | nil => v(vv)
    end.

Fixpoint subExpList (e : absExp) (l : list absExp) :=
    match e with
    | AbsConstVal v => AbsConstVal v
    | AbsVar v => AbsVar v
    | AbsQVar v => subVarList v l
    | AbsFun i ll => AbsFun i (map (fun x => subExpList x l) ll)
    end.

Fixpoint subStateList (s : absState) (l : list absExp) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (subStateList s1 l) (subStateList s2 l))
    | AbsOrStar s1 s2 => (AbsOrStar (subStateList s1 l) (subStateList s2 l))
    | AbsExistsT s => AbsExistsT (subStateList s (v(0)::(map (addExpVar 0) l)))
    | AbsExists e s => AbsExists (subExpList e l) (subStateList s (v(0)::(map (addExpVar 0) l)))
    | AbsAll e s => AbsAll (subExpList e l) (subStateList s (v(0)::(map (addExpVar 0) l)))
    | AbsEach e s => AbsEach (subExpList e l) (subStateList s (v(0)::(map (addExpVar 0) l)))
    | AbsEmpty => AbsEmpty
    | AbsAny => AbsAny
    | AbsNone => AbsNone
    | AbsLeaf i ll => AbsLeaf i (map (fun ee => subExpList ee l) ll)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (subExpList e1 l) (subExpList e2 l) (subExpList e3 l)
    | AbsMagicWand s1 s2 => AbsMagicWand (subStateList s1 l) (subStateList s2 l)
    | AbsUpdateVar s vv vall => AbsUpdateVar (subStateList s l) vv (subExpList vall l)
    | AbsUpdateWithLoc s vv vall => AbsUpdateWithLoc (subStateList s l) vv (subExpList vall l)
    | AbsUpdateLoc s vv vall => AbsUpdateLoc (subStateList s l) (subExpList vv l) (subExpList vall l)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (subStateList s1 l) (subStateList s2 l) (subStateList s3 l))
    | AbsClosure s ll => AbsClosure s (map (fun x => subExpList x l) ll)
   end.

Fixpoint expHeight (e : absExp) : nat :=
   match e with
   | AbsConstVal v => 0
   | AbsVar v => 0
   | AbsQVar v => (S v)
   | AbsFun i l => fold_left (fun n e => (n+e)) (map expHeight l) 0
   end.

Fixpoint hasVarExpList (l : list absExp) (v : id) :=
     match l with
     | (a::b) => if hasVarExp a v then true else hasVarExpList b v
     | nil => false
     end.

































































































