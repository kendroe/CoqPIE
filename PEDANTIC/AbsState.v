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

Definition evType := fst.

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
Inductive absExp {ev} {eq : ev -> ev -> bool}
                 { f : id -> list (@Value ev) -> (@Value ev) } : Type :=
   | AbsConstVal : (@Value ev) -> absExp
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

Fixpoint abs_ind' {ev} {eq : ev -> ev -> bool} { f : id -> list (@Value ev) -> (@Value ev) }
                  (P : @absExp ev eq f -> Prop)
                  (cbase : forall c, P (AbsConstVal c))
                  (vbase : forall id, P (AbsVar id))
                  (qbase : forall v, P (AbsQVar v))
                  (ff : forall id l, (All P l) -> P (AbsFun id l))
                  (e : @absExp ev eq f) : P e :=
    match e with
    | (AbsConstVal c) => cbase c
    | (AbsVar i) => vbase i
    | (AbsQVar v) => qbase v
    | (AbsFun i l) => ff i l
      ((fix go (ll : list (@absExp ev eq f)) : All P ll := match ll return All P ll with
                   | (fff::r) => conj (abs_ind' P cbase vbase qbase ff fff) (go r)
                   | nil => I
                   end) l)
    end.

Fixpoint value_ind' {ev}
                  (P : @Value ev -> Prop)
                  (nabase : forall c, P (NatValue c))
                  (nobase : P NoValue)
                  (obase : forall v, P (OtherValue v))
                  (ff : forall l, (All P l) -> P (ListValue l))
                  (e : @Value ev) : P e :=
    match e with
    | (NatValue n) => nabase n
    | NoValue => nobase
    | (OtherValue v) => obase v
    | (ListValue l) => ff l
      ((fix go (ll : list (@Value ev)) : All P ll := match ll return All P ll with
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

Fixpoint beq_val {t} {eq} (e1 : @Value t) (e2 : @Value t) : bool :=
    match (e1,e2) with
    | (NatValue v1,NatValue v2) => beq_nat v1 v2
    | (ListValue l1,ListValue l2) => beq_list (@beq_val t eq) l1 l2
    | (NoValue,NoValue) => true
    | (OtherValue v1,OtherValue v2) => eq v1 v2
    | _ => false
    end.

Fixpoint beq_absExp {ev} {eq} {x} (e1 : @absExp ev eq x) (e2 : @absExp ev eq x) : bool :=
   match e1 with
   | (AbsConstVal v) => match e2 with (AbsConstVal v2) => @beq_val ev eq v v2 | _ => false end
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
Fixpoint absEval {ev} {eq} {f} (env : id -> nat) (bindings : list (@Value ev)) (exp : @absExp ev eq f) : (@Value ev) :=
    match exp with
    | AbsConstVal v => v
    | AbsVar v => NatValue (env v)
    | AbsFun id pl => f id (map (absEval env bindings) pl)
    | AbsQVar n => nth n (rev bindings) NoValue
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

Inductive absState {ev}
                   {eq : ev -> ev -> bool}
                   { f : id -> list (@Value ev) -> (@Value ev) }
                   { t : id -> list (@Value ev) -> heap -> Prop }
                   { ac : id -> (id -> nat) -> (list (@Value ev)) -> (list (@Value ev)) -> (@absExp ev eq f) -> @Value ev -> Prop } :=
   | AbsExists :  (@absExp ev eq f) -> @absState ev eq f t ac -> absState
   | AbsExistsT : @absState ev eq f t ac -> absState
   | AbsAll : (@absExp ev eq f) -> @absState ev eq f t ac -> absState
   | AbsEach : (@absExp ev eq f) -> @absState ev eq f t ac -> absState
   | AbsStar : @absState ev eq f t ac -> @absState ev eq f t ac -> absState
   | AbsOrStar : @absState ev eq f t ac -> @absState ev eq f t ac -> absState
   | AbsEmpty : absState
   | AbsLeaf : id -> (list (@absExp ev eq f)) -> absState
   | AbsAccumulate : id -> @absExp ev eq f -> @absExp ev eq f -> @absExp ev eq f -> absState
   | AbsMagicWand : @absState ev eq f t ac -> @absState ev eq f t ac -> absState
   | AbsUpdateVar : @absState ev eq f t ac -> id -> (@absExp ev eq f) -> absState
   | AbsUpdState : @absState ev eq f t ac -> @absState ev eq f t ac -> @absState ev eq f t ac -> absState.

Notation "x '**' y" := (AbsStar x y)
  (at level 100, right associativity).

Notation "x '*\/*' y" := (AbsOrStar x y)
  (at level 110, right associativity).

(* Auxiliary functions--either used in realizedState below or in theorems involving realizeState
   (in other files) *)

Fixpoint instantiateExp {ev:Type} {eq} {t} (e : @absExp ev eq t) (val:@Value ev) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar v => match v with
                  | 0 => @AbsConstVal ev eq t val
                  | S x => AbsQVar x
                  end
   | AbsFun id pl => AbsFun id (map (fun x => instantiateExp x val) pl)
   end.

Fixpoint instantiateState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (val:@Value ev) : absState :=
   match s with
    | AbsStar s1 s2 => (AbsStar (instantiateState s1 val) (instantiateState s2 val))
    | AbsOrStar s1 s2 => (AbsOrStar (instantiateState s1 val) (instantiateState s2 val))
    | AbsExists e s => AbsExists (instantiateExp e val) (instantiateState s val)
    | AbsExistsT s => AbsExistsT (instantiateState s val)
    | AbsAll e s => AbsAll (instantiateExp e val) (instantiateState s val)
    | AbsEach e s => AbsEach (instantiateExp e val) (instantiateState s val)
    | AbsLeaf i el => AbsLeaf i (map (fun x => instantiateExp x val) el)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (instantiateExp e1 val) (instantiateExp e2 val) (instantiateExp e3 val)
    | AbsEmpty => @AbsEmpty ev eq f t ac
    | AbsMagicWand s1 s2 => AbsMagicWand (instantiateState s1 val) (instantiateState s2 val)
    | AbsUpdateVar s v vall => AbsUpdateVar (instantiateState s val) v (instantiateExp vall val)
    | AbsUpdState s11 s22 s33 => AbsUpdState (instantiateState s11 val) (instantiateState s22 val) (instantiateState s33 val)
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

Inductive realizeState {ev} {eq} {f} {t} {ac} : (@absState ev eq f t ac) -> list (@Value ev) -> state -> Prop :=
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
  | RSExists : forall (s:state) (a:absState) e (v : @Value ev) rl bindings,
               absEval (env_p _ _ s) bindings e = v ->
               v = (ListValue rl) ->
               (exists x, In x rl /\
                       realizeState a (bindings++(x::nil)) s) ->
               realizeState (AbsExists e a) bindings s
  | RSExistsU : forall s a bindings,
                 (exists x, realizeState a (bindings++(x::nil)) s) ->
                 realizeState (AbsExistsT a) bindings s
  | RSAccumulate : forall s e1 e2 e3 vl v3 i bindings,
                    absEval (env_p _ _ s) bindings e1 = (ListValue vl) ->
                    absEval (env_p _ _ s) bindings e3 = v3 ->
                    ac i (env_p _ _ s) bindings vl e2 v3 ->
                    realizeState (AbsAccumulate i e1 e2 e3) bindings s
  | RSAll : forall (s:state) (a:absState) e v rl bindings,
            absEval (env_p _ _ s) bindings e = v ->
            v = ListValue rl ->
            (forall x, In x rl ->
                       realizeState a (bindings++(x::nil)) s) ->
            realizeState (AbsAll e a) bindings s
  | RSEach : forall (s:state) (a:absState) e v rl states bindings l,
             absEval (env_p _ _ s) bindings e = v ->
             v = ListValue rl ->
             allFirsts rl l ->
             allSeconds states l ->
             (forall x y, In (x,y) l -> realizeState a (bindings++(x::nil)) y) ->
             fold_compose states s ->
             realizeState (AbsEach e a) bindings s
  | RSEmpty : forall s bindings,
              (forall x, snd s x=None) -> realizeState AbsEmpty bindings s
  | RSR : forall s el vl i bindings,
          map (absEval (env_p _ _ s) bindings) el = vl ->
          t i vl (snd s) ->
          realizeState (AbsLeaf i el) bindings s
  | RSMagicWand : forall s1 s2 as1 as2 s3 bindings,
                  realizeState as1 bindings s1 ->
                  realizeState as2 bindings s2 ->
                  concreteCompose s3 s2 s1 ->
                  realizeState (AbsMagicWand as1 as2) bindings s3
  | RSUpdateVar : forall s s1 as1 vv valaa valc bindings,
                  realizeState as1 bindings s1 ->
                  (NatValue valc) = absEval (env_p _ _ s) bindings valaa ->
                  (heap_p _ _ s) = (heap_p _ _ s1) ->
                  (override (env_p _ _ s) vv valc)= (env_p _ _ s1) ->
                  realizeState (AbsUpdateVar as1 vv valaa) bindings s1
  | RSUpdState : forall s1 s2 s3 as1 as2 as3 s4 s5 bindings,
                 realizeState as1 bindings s1 ->
                 realizeState as2 bindings s2 ->
                 realizeState as3 bindings s3 ->
                 concreteCompose s4 s2 s1 ->
                 concreteCompose s4 s3 s5 ->
                 realizeState (AbsUpdState as1 as2 as3) bindings s5.

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

Fixpoint pushAbsVar {T} {eq} {f} (e : @absExp T eq f) : @absExp T eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar vv => AbsVar vv
   | AbsQVar v => AbsQVar (S v)
   | AbsFun i el => AbsFun i (map pushAbsVar el)
   end.

Fixpoint pushAbsVarState {EV} {EQ} {F} {T} {AC} (s : @absState EV EQ F T AC) : @absState EV EQ F T AC :=
   match s with
    | AbsStar s1 s2 => (AbsStar (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsOrStar s1 s2 => (AbsOrStar (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsExists e s => AbsExists (pushAbsVar e) (pushAbsVarState s)
    | AbsExistsT s => AbsExistsT (pushAbsVarState s)
    | AbsAll e s => AbsAll (pushAbsVar e) (pushAbsVarState s)
    | AbsEach e s => AbsEach (pushAbsVar e) (pushAbsVarState s)
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (pushAbsVar e1) (pushAbsVar e2) (pushAbsVar e3)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i el => AbsLeaf i (map pushAbsVar el)
    | AbsMagicWand s1 s2 => (AbsMagicWand (pushAbsVarState s1) (pushAbsVarState s2))
    | AbsUpdateVar s v vall => (AbsUpdateVar (pushAbsVarState s) v (pushAbsVar vall))
    | AbsUpdState s1 s2 s3 => (AbsUpdState (pushAbsVarState s1) (pushAbsVarState s2) (pushAbsVarState s3))
   end.

Fixpoint quantifyAbsVar {EV} {EQ} {T} (e : @absExp EV EQ T) (v:id) : @absExp EV EQ T :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar vv => if beq_id vv v then AbsQVar 0 else AbsVar vv
   | AbsQVar v => AbsQVar (S v)
   | AbsFun i el => AbsFun i (map (fun x => quantifyAbsVar x v) el)
   end.

Fixpoint quantifyAbsVarState {EV} {EQ} {F} {T} {AC} (s : @absState EV EQ F T AC) (v:id) : @absState EV EQ F T AC :=
   match s with
    | AbsStar s1 s2 => (AbsStar (quantifyAbsVarState s1 v) (quantifyAbsVarState s2 v))
    | AbsOrStar s1 s2 => (AbsOrStar (quantifyAbsVarState s1 v) (quantifyAbsVarState s2 v))
    | AbsExists e s => AbsExists (quantifyAbsVar e v) (quantifyAbsVarState s v)
    | AbsExistsT s => AbsExistsT (quantifyAbsVarState s v)
    | AbsAll e s => AbsAll (quantifyAbsVar e v) (quantifyAbsVarState s v)
    | AbsEach e s => AbsEach (quantifyAbsVar e v) (quantifyAbsVarState s v)
    | AbsEmpty => AbsEmpty
    | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (quantifyAbsVar e1 v) (quantifyAbsVar e2 v) (quantifyAbsVar e3 v)
    | AbsLeaf i el => AbsLeaf i (map (fun x => quantifyAbsVar x v) el)
    | AbsMagicWand s1 s2 => (AbsMagicWand (quantifyAbsVarState s1 v) (quantifyAbsVarState s2 v))
    | AbsUpdateVar s v vall => (AbsUpdateVar (quantifyAbsVarState s v) v (quantifyAbsVar vall v))
    | AbsUpdState s1 s2 s3 => (AbsUpdState (quantifyAbsVarState s1 v) (quantifyAbsVarState s2 v) (quantifyAbsVarState s3 v))
   end.

Fixpoint convertAbsValue {ev} {ev'} (m : ev -> ev') (v : @Value ev) : @Value ev' :=
   match v with
   | NatValue v => NatValue v
   | ListValue l => ListValue (map (convertAbsValue m) l)
   | NoValue => NoValue
   | OtherValue v => OtherValue (m v)
   end.

Fixpoint convertAbsExp {ev} {eq} {f} {ev'} {eq'} {f'} (m : ev -> ev') (e : @absExp ev eq f) : @absExp ev' eq' f' :=
   match e with
   | AbsConstVal v => @AbsConstVal ev' eq' f' (convertAbsValue m v)
   | AbsVar v => AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun id pl => AbsFun id (map (convertAbsExp m) pl)
   end.


Fixpoint subst {ev} {eq} {f} (e : @absExp ev eq f ) (n: nat) (val:@absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal x => AbsConstVal x
   | AbsVar v => AbsVar v
   | AbsQVar v => if beq_nat v n then val else (AbsQVar v)
   | AbsFun i l => AbsFun i (map (fun x => subst x n val) l)
   end.

Fixpoint substState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (n : nat) (val:@absExp ev eq f) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (substState s1 n val) (substState s2 n val))
    | AbsOrStar s1 s2 => (AbsOrStar (substState s1 n val) (substState s2 n val))
    | AbsExistsT s => AbsExistsT (substState s n val)
    | AbsExists e s => AbsExists (subst e n val) (substState s n val)
    | AbsAll e s => AbsAll (subst e n val) (substState s n val)
    | AbsEach e s => AbsEach (subst e n val) (substState s n val)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (fun x => subst x n val) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (subst e1 n val) (subst e2 n val) (subst e3 n val)
    | AbsMagicWand s1 s2 => AbsMagicWand (substState s1 n val) (substState s2 n val)
    | AbsUpdateVar s v   vall => AbsUpdateVar (substState s n val) v (subst vall n val)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (substState s1 n val) (substState s2 n val) (substState s3 n val))
   end.

Fixpoint substVar {ev} {eq} {f} (e : @absExp ev eq f) (n: id) (val:@absExp ev eq f) : absExp :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => if beq_id v n then val else AbsVar v
   | AbsQVar v => AbsQVar v
   | AbsFun i l => AbsFun i (map (fun x => substVar x n val) l)
   end.

Fixpoint substVarState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (n : id) (val:@absExp ev eq f) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (substVarState s1 n val) (substVarState s2 n val))
    | AbsOrStar s1 s2 => (AbsOrStar (substVarState s1 n val) (substVarState s2 n val))
    | AbsExistsT s => AbsExistsT (substVarState s n val)
    | AbsExists e s => AbsExists (substVar e n val) (substVarState s n val)
    | AbsAll e s => AbsAll (substVar e n val) (substVarState s n val)
    | AbsEach e s => AbsEach (substVar e n val) (substVarState s n val)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (fun x => substVar x n val) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (substVar e1 n val) (substVar e2 n val) (substVar e3 n val)
    | AbsMagicWand s1 s2 => AbsMagicWand (substVarState s1 n val) (substVarState s2 n val)
    | AbsUpdateVar s v   vall => AbsUpdateVar (substVarState s n val) v (substVar vall n val)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (substVarState s1 n val) (substVarState s2 n val) (substVarState s3 n val))
   end.

Fixpoint hasVnExp {ev} {eq} {f} (e : @absExp ev eq f) (v : absVar) : bool :=
   match e with
   | AbsConstVal v => false
   | AbsVar vv => false
   | AbsQVar vv => beq_nat vv v
   | AbsFun i l => (fix go l := match l with
                               | (f::r) => if hasVnExp f v then true else go r
                               | nil => false
                               end) l
   end.

Fixpoint hasVnState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (v : absVar) :=
    match s with
    | AbsStar s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsOrStar s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsExistsT s => hasVnState s v
    | AbsExists e s => if hasVnExp e v then true else hasVnState s v
    | AbsAll e s => if hasVnExp e v then true else hasVnState s v
    | AbsEach e s => if hasVnExp e v then true else hasVnState s v
    | AbsLeaf i l => (fix go l := match l with
                               | (f::r) => if hasVnExp f v then true else go r
                               | nil => false
                               end) l
    | AbsAccumulate id e1 e2 e3 => if hasVnExp e1 v then true else
                                   if hasVnExp e2 v then true else
                                   if hasVnExp e3 v then true else false
    | AbsMagicWand s1 s2 => if (hasVnState s1 v:bool) then true else hasVnState s2 v
    | AbsUpdateVar s vv vall => if (hasVnState s v:bool) then true else hasVnExp vall v
    | AbsUpdState s1 s2 s3 => if (hasVnState s1 v:bool) then true else
                              if (hasVnState s2 v:bool) then true else
                              hasVnState s3 v
    | _ => false
    end.

Inductive an_empty_state {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> Prop :=
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

Fixpoint removeExpVar {ev} {eq} {f} (v : nat) (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if ble_nat vv v then AbsQVar vv else AbsQVar (vv-1)
   | AbsFun i l => AbsFun i (map (removeExpVar v) l)
   end.

Fixpoint removeStateVar {ev} {eq} {f} {t} {ac} (n : nat) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (removeStateVar n s1) (removeStateVar n s2))
    | AbsOrStar s1 s2 => (AbsOrStar (removeStateVar n s1) (removeStateVar n s2))
    | AbsExistsT s => AbsExistsT (removeStateVar n s)
    | AbsExists e s => AbsExists (removeExpVar n e) (removeStateVar n s)
    | AbsAll e s => AbsAll (removeExpVar n e) (removeStateVar n s)
    | AbsEach e s => AbsEach (removeExpVar n e) (removeStateVar n s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (removeExpVar n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (removeExpVar n e1) (removeExpVar n e2) (removeExpVar n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (removeStateVar n s1) (removeStateVar n s2)
    | AbsUpdateVar s v   vall => AbsUpdateVar (removeStateVar n s) v (removeExpVar n vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (removeStateVar n s1) (removeStateVar n s2) (removeStateVar n s3))
   end.

Fixpoint addExpVar {ev} {eq} {f} (v : nat) (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if ble_nat v vv then AbsQVar (vv+1) else AbsQVar vv
   | AbsFun i l => AbsFun i (map (addExpVar v) l)
   end.

Fixpoint addStateVar {ev} {eq} {f} {t} {ac} (n : nat) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (addStateVar n s1) (addStateVar n s2))
    | AbsOrStar s1 s2 => (AbsOrStar (addStateVar n s1) (addStateVar n s2))
    | AbsExistsT s => AbsExistsT (addStateVar n s)
    | AbsExists e s => AbsExists (addExpVar n e) (addStateVar n s)
    | AbsAll e s => AbsAll (addExpVar n e) (addStateVar n s)
    | AbsEach e s => AbsEach (addExpVar n e) (addStateVar n s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (addExpVar n) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (addExpVar n e1) (addExpVar n e2) (addExpVar n e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (addStateVar n s1) (addStateVar n s2)
    | AbsUpdateVar s v   vall => AbsUpdateVar (addStateVar n s) v (addExpVar n vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (addStateVar n s1) (addStateVar n s2) (addStateVar n s3))
   end.

Fixpoint replaceExpVar {ev} {eq} {f} (v : nat) (rr : @absExp ev eq f) (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => if beq_nat v vv then rr else AbsQVar vv
   | AbsFun i l => AbsFun i (map (replaceExpVar v rr) l)
   end.

Fixpoint replaceStateVar {ev} {eq} {f} {t} {ac} (n : nat) (rr : @absExp ev eq f) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceStateVar n rr s1) (replaceStateVar n rr s2))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceStateVar n rr s1) (replaceStateVar n rr s2))
    | AbsExistsT s => AbsExistsT (replaceStateVar n rr s)
    | AbsExists e s => AbsExists (replaceExpVar n rr e) (replaceStateVar n rr s)
    | AbsAll e s => AbsAll (replaceExpVar n rr e) (replaceStateVar n rr s)
    | AbsEach e s => AbsEach (replaceExpVar n rr e) (replaceStateVar n rr s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (replaceExpVar n rr) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExpVar n rr e1) (replaceExpVar n rr e2) (replaceExpVar n rr e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceStateVar n rr s1) (replaceStateVar n rr s2)
    | AbsUpdateVar s v   vall => AbsUpdateVar (replaceStateVar n rr s) v (replaceExpVar n rr vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (replaceStateVar n rr s1) (replaceStateVar n rr s2) (replaceStateVar n rr s3))
   end.

Fixpoint replaceExpExp {ev} {eq} {f} (v : @absExp ev eq f) (rr : @absExp ev eq f) (e : @absExp ev eq f) : @absExp ev eq f :=
   if beq_absExp v e then rr else 
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => AbsQVar vv
   | AbsFun i l => AbsFun i (map (replaceExpExp v rr) l)
   end.

Fixpoint replaceStateExp {ev} {eq} {f} {t} {ac} (v : @absExp ev eq f) (rr : @absExp ev eq f) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (replaceStateExp v rr s1) (replaceStateExp v rr s2))
    | AbsOrStar s1 s2 => (AbsOrStar (replaceStateExp v rr s1) (replaceStateExp v rr s2))
    | AbsExistsT s => AbsExistsT (replaceStateExp v rr s)
    | AbsExists e s => AbsExists (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsAll e s => AbsAll (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsEach e s => AbsEach (replaceExpExp v rr e) (replaceStateExp v rr s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map (replaceExpExp v rr) l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (replaceExpExp v rr e1) (replaceExpExp v rr e2) (replaceExpExp v rr e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (replaceStateExp v rr s1) (replaceStateExp v rr s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (replaceStateExp v rr s) vv (replaceExpExp v rr vall)
    | AbsUpdState s1 s2 s3 =>  (AbsUpdState (replaceStateExp v rr s1) (replaceStateExp v rr s2) (replaceStateExp v rr s3))
   end.

Fixpoint N {ev} {eq} {f} (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => AbsVar v
   | AbsQVar vv => AbsQVar (S vv)
   | AbsFun i l => AbsFun i (map N l)
   end.

Fixpoint NS {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
   match s with
    | AbsStar s1 s2 => (AbsStar (NS s1) (NS s2))
    | AbsOrStar s1 s2 => (AbsOrStar (NS s1) (NS s2))
    | AbsExistsT s => AbsExistsT (NS s)
    | AbsExists e s => AbsExists (N e) (NS s)
    | AbsAll e s => AbsAll (N e) (NS s)
    | AbsEach e s => AbsEach (N e) (NS s)
    | AbsEmpty => AbsEmpty
    | AbsLeaf i l => AbsLeaf i (map N l)
    | AbsAccumulate id e1 e2 e3 => AbsAccumulate id (N e1) (N e2) (N e3)
    | AbsMagicWand s1 s2 => AbsMagicWand (NS s1) (NS s2)
    | AbsUpdateVar s vv vall => AbsUpdateVar (NS s) vv (N vall)
    | AbsUpdState s1 s2 s3 =>  AbsUpdState (NS s1) (NS s2) (NS s3)
   end.

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

Definition supportsFunctionality ev eq (f : id -> list (@Value ev) -> (@Value ev)) (f_count : nat)
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
        ac' (Id i) env b vl e v -> i < ac_count -> ac (Id i) env (map (convertAbsValue mfun) b) (map (convertAbsValue mfun) vl) (convertAbsExp mfun e) (convertAbsValue mfun v)).

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

(*Theorem composeEmptyRight {ev} {eq} {f} {t} {ac} :
    forall (s : @absState ev eq f t ac) state bindings,
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





















