(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * Simplify.v
 * This file contains tactics for simplifying states.  Simplification is designed to
 * return equivalent states (rather than an implied state).  Hence it is applicable
 * in either a hypothesis or goal.
 *
 * Some key definitions
 *    simplifyContext
 *    simplifyExpression
 *    simplifyState'
 *    simplifyState''
 *    simplifyState'''
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export ImpHeap.
Require Export AbsState.
Require Export AbsStateInstance.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Eqdep.
Require Export AbsExecute.
Require Export PickElement.

Inductive Context :=
    | StateComponent : absState -> Context
    | AllContext : absExp -> Context -> Context
    | NonZeroExpression : absExp -> Context
    | Domain : nat -> absExp -> Context.

Fixpoint pushContext (c : Context) :=
    match c with
    | StateComponent s => StateComponent (addStateVar 0 s)
    | AllContext e c => AllContext (addExpVar 0 e) (pushContext c)
    | NonZeroExpression e => NonZeroExpression (addExpVar 0 e)
    | Domain n e => Domain (S n) (addExpVar 0 e)
    end.

Fixpoint pushContextList (c : list Context) :=
    map pushContext c.

Fixpoint buildExpressionContext (e: absExp) (neg : bool) : list Context :=
   if neg then
        match e with
        | AbsFun (AbsOrId) (p::q::nil) => (buildExpressionContext p true)++(buildExpressionContext q true)
        | AbsFun (AbsImplyId) (p::q::nil) => (buildExpressionContext p false)++(buildExpressionContext q true)
        | ~~e => ((NonZeroExpression e)::nil)
        | _ => ((NonZeroExpression (~~e))::nil)
        end
   else
        match e with
        | AbsFun (AbsAndId) (p::q::nil) => (buildExpressionContext p false)++(buildExpressionContext q false)
        | _ => ((NonZeroExpression e)::nil)
        end.

Fixpoint buildNegStateContext (s : absState) : list Context :=
    match s with
    | AbsOrStar l r => (buildNegStateContext l)++(buildNegStateContext r)
    | AbsLeaf (AbsPredicate) (x::nil) => buildExpressionContext x true
    | _ => nil
    end.

Fixpoint buildStateContext (s : absState) : list Context :=
    match s with
    | AbsStar l r => (buildStateContext l)++(buildStateContext r)
    | AbsLeaf (AbsPredicate) (x::nil) => buildExpressionContext x false
    | AbsAll e s => map (fun x => (AllContext e x)) (buildStateContext s)
    | _ => (StateComponent s)::nil
    end.

Fixpoint enterAll (e : absExp) (context : list Context) :=
    match context with
    | nil => nil
    | ((AllContext ee cc)::r) => if beq_absExp ee e then cc::(enterAll e r) else enterAll e r
    | (f::r) => (pushContext f)::(enterAll e r)
    end.

Fixpoint enterQuant (context : list Context) :=
    match context with
    | nil => nil
    | ((AllContext ee cc)::r) => enterQuant r
    | (f::r) => (pushContext f)::(enterQuant r)
    end.

Fixpoint findMember (base : absExp) (context : list absExp) :=
   match context with
   | (AbsFun (AbsMemberId) (element::tree))::r => if beq_absExp base element then
                                                      Some tree
                                                  else findMember base r
   | (_::r) => findMember base r
   | nil => None
   end.

Fixpoint hasCell (state : absState) (loc : absExp) :=
   match state with
   | AbsLeaf (Id 3) (*AbsCellId*) (l::v::nil) => beq_absExp l loc
   | AbsExistsT s => hasCell s loc
   | AbsAll e s => hasCell s loc
   | AbsExists e s => hasCell s loc
   | AbsEach e s => hasCell s loc
   | AbsStar l r => if (hasCell l loc:bool) then true else hasCell r loc
   | _ => false
   end.

Fixpoint findSmallerVar (v : id) (c : list Context) : absExp :=
    match c with
    | (NonZeroExpression ((AbsVar x)====(AbsConstVal z))::r) => if beq_id x v then (AbsConstVal z) else findSmallerVar v r
    | (NonZeroExpression ((AbsConstVal z)====(AbsVar x))::r) => if beq_id x v then (AbsConstVal z) else findSmallerVar v r
    | (NonZeroExpression ((AbsVar (Id x))====(AbsVar (Id y)))::r) =>
      if beq_id (Id x) v then
          (if ble_nat x y then findSmallerVar v r else (AbsVar (Id y)))
      else (if beq_id (Id y) v then
          (if ble_nat x y then findSmallerVar v r else (AbsVar (Id y)))
      else findSmallerVar v r)
    | (_::r) => findSmallerVar v r
    | _ => AbsVar v
    end.

Fixpoint findVar (e : absExp) (c : list Context) : absExp :=
    match c with
    | (NonZeroExpression ((AbsVar x)====xx)::r) => if beq_absExp xx e then (AbsVar x) else findVar e r
    | (NonZeroExpression (xx====(AbsVar x))::r) => if beq_absExp xx e then (AbsVar x) else findVar e r
    | (_::r) => findVar e r
    | _ => e
    end.

Fixpoint findVarSubst (vv: id) (c : list Context) : absExp :=
    match c with
    | (NonZeroExpression ((AbsVar x)====#c)::r) => if beq_id x vv then #c else (AbsVar vv)
    | (NonZeroExpression (#c====(AbsVar x))::r) => if beq_id x vv then #c else (AbsVar vv)
    | (_::r) => findVarSubst vv r
    | _ => (AbsVar vv)
    end.

Fixpoint noSmallerQuantVars (n : nat) (e : absExp) : bool :=
    match e with
    | AbsVar _ => true
    | AbsQVar x => if ble_nat x n then false else true
    | AbsConstVal _ => true
    | AbsFun i l => (fix go l := match l with
                                 | nil => true
                                 | (f::r) => if noSmallerQuantVars n f then go r else false
                                 end) l
    end.

Fixpoint subQVar (v : nat) (c : list Context) : absExp :=
    match c with
    | (NonZeroExpression ((AbsQVar x)====y)::r) => if beq_nat v x then (if noSmallerQuantVars x y then y else subQVar v r) else (match y with
                                      | AbsQVar zz => if beq_nat zz v then (if ble_nat zz x then AbsQVar x else subQVar v r) else subQVar v r
                                      | _ => subQVar v r
                                      end)
    | (NonZeroExpression (y====(AbsQVar x))::r) => if beq_nat v x then (if noSmallerQuantVars x y then y else subQVar v r) else subQVar v r
    | (_::r) => subQVar v r
    | _ => AbsQVar v
    end.

Fixpoint pickCt (x : absExp) (context : list Context) : bool :=
  match context with
  | nil => false
  | ((StateComponent (l |-> f))::r) => if beq_absExp x f then true else pickCt x r
  | ((StateComponent (TREE(root,ff,size,fields)))::r) => if beq_absExp ff x then true else pickCt x r
  | (_::r) => pickCt x r
  end.

Fixpoint pickRt (x : absExp) (context : list Context) : bool :=
  match context with
  | nil => false
  | ((StateComponent ((l++++#0) |-> f))::r) => if beq_absExp x f then true
                                               else if beq_absExp x l then true
                                               else if beq_absExp nth(x,#0) f then true else pickRt x r
  | ((StateComponent (l |-> f))::r) => if beq_absExp x f then true
                                       else if beq_absExp x l then true
                                       else if beq_absExp nth(x,#0) f then true
                                       else pickRt x r
  | ((StateComponent (TREE(root,ff,size,fields)))::r) => if beq_absExp ff x then true else pickRt x r
  | (_::r) => pickRt x r
  end.

Fixpoint allPresent (l : list absExp) (e: absExp) (context : list Context) : bool :=
  match l with
  | nil => true
  | ((AbsVar x)::r) => allPresent r e context
  | (x::r) => if beq_absExp e x then allPresent r e context else if pickCt x context then allPresent r e context else false
  end.

Fixpoint allUsed (l : list absExp) (e: absExp) (context : list Context) : bool :=
  match l with
  | nil => true
  | ((!!v)::r) => allUsed r e context
  | (x::r) => if beq_absExp e x then allUsed r e context else if pickRt x context then allUsed r e context else false
  end.

Fixpoint findDomain (n : nat) (context : list Context) :=
    match context with
    | nil => None
    | ((Domain v (AbsFun (AbsRangeSetId) (d::nil)))::r) => if beq_nat v n then Some d else findDomain n r
    | (_::r) => findDomain n r
    end.

(*Fixpoint buildDomainList {ev} {eq} {f} {t} {ac} (l : list (@absExp ev eq f)) (context : list (@Context ev eq f t ac)) :=
  match l with
  | ((AbsFun (AbsRangeSetId) (f::nil))::r) => match findDomain n context with
                        | Some d => Some (d,r)
                        | None => match buildDomainList n r context with
                                  | Some (d,r) => Some (d,((AbsQVar f)::r))
                                  | None => None
                                  end
                        end
  | (f::r) => match buildDomainList n r context with
              | Some (d,r) => Some (d,(f::r))
              | None => None
              end
  | nil => None
  end.*)

Fixpoint hasEquality (c : list Context) (e1: absExp) (e2: absExp) :=
    match c with
    | nil => false
    | ((NonZeroExpression (AbsFun (AbsEqualId) (l::r::nil)))::rest) =>
            if (beq_absExp l e1 && beq_absExp r e2) || (beq_absExp l e2 && beq_absExp r e1) then true
            else hasEquality rest e1 e2
    | (_::r) => hasEquality r e1 e2
    end.

Fixpoint hasNonZero (c : list Context) (e: absExp) :=
    match c with
    | nil => false
    | ((NonZeroExpression x)::rest) =>
            if beq_absExp e x then true
            else hasNonZero rest e
    | (_::r) => hasNonZero r e
    end.

Fixpoint simplifyExp
                            (rule : (list Context)
                                -> absExp -> absExp)
                            (context : list Context)
                            (e : absExp) : absExp :=
    rule context (match e with
                    | AbsFun (AbsImplyId) (p::q::nil) =>
                             match simplifyExp rule
                                   ((buildExpressionContext q true)++context) p with
                                   | #0 => #1
                                   | #x => simplifyExp rule context q
                                   | x => x -->> (simplifyExp rule
                                                  ((buildExpressionContext x false)++context) q)
                             end
                    | AbsFun (AbsAndId) (p::q::nil) =>
                             match simplifyExp rule
                                   ((buildExpressionContext q false)++context) p with
                                   | #0 => #0
                                   | #x => simplifyExp rule context q
                                   | x => x //\\ (simplifyExp rule
                                                  ((buildExpressionContext x false)++context) q)
                             end
                    | AbsFun (AbsOrId) (p::q::nil) =>
                             match simplifyExp rule
                                   ((buildExpressionContext q true)++context) p with
                                   | #0 => simplifyExp rule context q
                                   | #x => #x
                                   | x => x \\// (simplifyExp rule
                                                  ((buildExpressionContext x true)++context) q)
                             end
                    | AbsFun (AbsIteId) (p::q::r::nil) =>
                             match (simplifyExp rule context p) with
                             | #x => if beq_nat x 0
                                     then (simplifyExp rule context r)
                                     else (simplifyExp rule context q)
                             | x           => (AbsFun (AbsIteId) 
                                                 (x::(simplifyExp rule
                                                       ((buildExpressionContext x false)++context) q)::
                                                     (simplifyExp rule
                                                       ((buildExpressionContext x true)++context) r)::nil))
                             end
                    | AbsFun i l => (AbsFun i (map (simplifyExp rule context) l))
                    | x => x
                   end).

(*Fixpoint process_nth {ev:Type} {eq} {f} (p : @absExp ev eq f) (q : @absExp ev eq f) :=
    match p with
    | AbsFun ff l =>
      if beq_id ff AbsNthId then
      match q with
      | AbsConstVal x =>
                        match x with
                        | NatValue n => nth n l (@AbsConstVal ev eq f (NatValue n))
                        | _ =>  (@AbsConstVal ev eq f (NatValue 666))
                        end
      | x => AbsFun (AbsNthId) (p::q::nil)
      end else AbsFun (AbsNthId) (p::q::nil)
    | x => AbsFun (AbsNthId) (p::q::nil)
    end.*)

Fixpoint findArray (context : list Context)
                   (base : absExp) :=
    match context with
    | nil => None
    | ((StateComponent (ARRAY(_,size,b)))::r) => if beq_absExp b base then
                                                     Some size else findArray r base
    | (_::r) => findArray r base
    end.

Fixpoint findLess (context : list Context)
                  (loc : absExp) (size : absExp) : bool :=
    match context with
    | nil => false
    | (NonZeroExpression (l <<<< s)::r) => if beq_absExp l loc then if beq_absExp s size then true
                                           else findLess r loc size else findLess r loc size
    | (_::r) => findLess r loc size
    end.

Fixpoint validReplace (context : list Context)
                      (base : absExp) (loc : absExp) : bool :=
    match findArray context base with
    | Some size => findLess context loc size
    | None => false
    end.

Fixpoint rangeBotExclude (n:nat) (s:absExp) (e:absExp)
                         (v1:absExp) (v2:absExp) :=
     match v1 with
     | AbsQVar m => if beq_nat (S m) n then if beq_absExp (v2++++#1) s then true else false
                    else false
     | _ => false
     end.

Fixpoint rangeExclude (n:nat) (s:absExp) (e:absExp)
                      (v1:absExp) (v2:absExp) :=
     match v1 with
     | AbsQVar m => if beq_nat (S m) n then if beq_absExp v2 e then true else rangeBotExclude n s e v1 v2
                    else rangeBotExclude n s e v1 v2
     | _ => rangeBotExclude n s e v1 v2
     end.

Fixpoint notEqual (context : list Context)
                  (e1 : absExp) (e2 : absExp) : bool :=
    match context with
    | (NonZeroExpression (~~(l====r))::rest) => match beq_absExp e1 l,beq_absExp e2 r with
                                                | true,true => true
                                                | _,_ => match beq_absExp e1 r,beq_absExp e2 l with
                                                         | true,true => true
                                                         | _,_ => notEqual rest e1 e2
                                                         end
                                                end
    | (Domain n (range(s,e))::rest) => if rangeExclude n s e e1 e2 then true else
                                       if rangeExclude n s e e2 e1 then true else notEqual rest e1 e2
    | (_::rest) => notEqual rest e1 e2
    | nil => false
    end.

Fixpoint boolExp (e : absExp) :=
    match e with
    | ~~x => true
    | a====b => true
    | a<<<<b => true
    | _ => false
    end.

Fixpoint inversionExp (a : absExp) (b : absExp)  :=
    match a,b with
    | x,~~y => beq_absExp x y
    | ~~x,y => beq_absExp x y
    | (a\\//b),(c//\\d) => ((inversionExp a c)&&(inversionExp b d)) || ((inversionExp a d)&&(inversionExp b c))
    | (a//\\b),(c\\//d) => ((inversionExp a c)&&(inversionExp b d)) || ((inversionExp a d)&&(inversionExp b c))
    | _,_ => false
    end.

Fixpoint basicExpRule1
                       (context : list Context)
                       (e : absExp) : absExp :=
         match e with
         | AbsFun (AbsEqualId) ((#a)::(#b)::nil) => if beq_nat a b then (#1) else (#0)
         | AbsFun (AbsEqualId) ((#0)::(a++++b)::nil) => ((#0====a) //\\ (#0====b))
         | AbsFun (AbsEqualId) ((#a)::(exp++++(#b))::nil) => if ble_nat b a then (#(a-b)====exp) else e
         | AbsFun (AbsEqualId) (e1::e2::nil) => if (beq_absExp e1 e2)
                                                then  AbsConstVal (NatValue 1)
                                                else if hasEquality context e1 e2 then (#1)
                                                else if hasNonZero context (e1<<<<e2) || hasNonZero context (e2<<<<e1) then (#0)
                                                else e1====e2
         | ((#a) <<<< (#b)) => if ble_nat b a then (#0) else (#1)
         | (p <<<< (#0)) => #0
         | AbsFun (AbsNotId) ((#0<<<<b)::nil) => (b====#0)
         | AbsFun (AbsNotId) ((#0====b)::nil) => (#0<<<<b)
         | AbsFun (AbsNotId) ((b====#0)::nil) => (#0<<<<b)
         | AbsFun (AbsNotId) ((#0)::nil) => (#1)
         | AbsFun (AbsNotId) ((#1)::nil) => (#0)
         | AbsFun (AbsNotId) (p::nil) =>
                 match p with
                 | AbsFun (AbsAndId) l => (AbsFun (AbsOrId) (map (fun x => (~~x)) l))
                 | AbsFun (AbsOrId) l => (AbsFun (AbsAndId) (map (fun x => (~~x)) l))
                 | AbsFun (AbsNotId) (x::nil) => x
                 | x => ~~x
                 end
         | AbsFun (AbsPlusId) (p::(#0)::nil) => p
         | AbsFun (AbsPlusId) ((#0)::p::nil) => p
         | AbsFun (AbsAndId) ((AbsFun (AbsEqualId) (x::(#0)::nil))::(AbsFun (AbsEqualId) (y::(#0)::nil))::nil) =>
               if hasNonZero context (x \\// y) then #0 else e
         | AbsFun (AbsAndId) (p::q::nil) =>
                 match q with
                 | #0 => #0
                 | #1 => match p with
                         | a====b => a====b
                         | a<<<<b => a<<<<b
                         | ~~ a => ~~a
                         | _ => p //\\ #1
                         end
                 | x => p //\\ x
                 end
         | AbsFun (AbsOrId) (p::q::nil) =>
                 match p,q with
                 | p,#0 => p
                 | p,#1 => match p with
                         | a====b => #1
                         | a<<<<b => #1
                         | ~~ a => #1
                         | _ //\\ (~~ _) => #1
                         | _ => p \\// #1
                         end
                 (*| (a//\\b),(c//\\d) =>
                   match a with
                   | (a//\\b1) => if beq_absExp a c && boolExp a && inversionExp (b1//\\b) d then a else ((a//\\b1)//\\b)\\//(c//\\(d//\\e))
                   | a =>  if beq_absExp a c && boolExp a && inversionExp b d then a else (a//\\b)\\//(c//\\(d//\\e))
                   end*)
                 | p,x => p \\// x
                 end
         | AbsFun (AbsNthId) (p::q::nil) =>
                match p,q with
                 | (AbsFun (AbsReplaceNthId) (base::loc::val::nil)),loc2 =>
                   if beq_absExp loc loc2 then
                       if validReplace context base loc then
                           val
                       else
                           (AbsFun (AbsNthId) ((AbsFun (AbsReplaceNthId) (base::loc::val::nil))::loc2::nil))
                   else if notEqual context loc loc2 then
                       (AbsFun (AbsNthId) (base::loc2::nil))
                   else
                       (AbsFun (AbsNthId) ((AbsFun (AbsReplaceNthId) (base::loc::val::nil))::loc2::nil))
                 | (AbsFun ff l),(AbsConstVal x) =>
                     if beq_id ff AbsListId then
                        match x with
                        | NatValue n => nth n l (AbsConstVal NoValue)
                        | _ =>  (AbsConstVal NoValue)
                        end
                     else (AbsFun (AbsNthId) (p::q::nil))
                 | _,a => (AbsFun (AbsNthId) (p::q::nil))
                 end
         | AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil) =>
                 if beq_absExp ff f' then AbsFun (AbsListId) (ff::r)
                 else match f' with
                      | AbsQVar m => match findDomain m context with
                                     | Some d => if allUsed r d context then
                                                     (AbsFun (AbsFindId) (d::f'::nil))
                                                 else
                                                     (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                                     | None => (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                                     end
                      | _ => (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                      end
         | AbsFun (AbsFindId) ((AbsFun (AbsFindId) (base::(AbsQVar v1)::nil))::(AbsQVar v2)::nil) =>
                  match findDomain v2 context,findDomain v1 context with
                  | Some (AbsFun (AbsFindId) (base::(AbsQVar v1)::nil)), Some b2 =>
                        if beq_absExp base b2 then (AbsFun (AbsFindId) (base::(AbsQVar v2)::nil))
                        else e
                  | _,_ => e
                  end
         | AbsFun (AbsLessId) (l::r::nil) => if hasEquality context l r then (#0)
                                             else AbsFun (AbsLessId) (l::r::nil)
         | AbsFun (AbsRangeSetId) ((AbsVar x)::nil) => (AbsConstVal (ListValue nil))
         | AbsFun (AbsRangeSetId) ((AbsConstVal (ListValue nil))::nil) => (AbsConstVal (ListValue nil))
         | AbsFun (AbsIteId) ((AbsFun (AbsEqualId) (l::r::nil))::(#1)::(#0)::nil) =>
                  (AbsFun (AbsEqualId) (l::r::nil))
         | AbsFun (AbsIteId) (c::(#1)::(#0)::nil) => (AbsFun (AbsLessId) ((#0)::c::nil))
         | AbsVar v => findVarSubst v context
         | AbsQVar v => subQVar v context
         | x => x
         end.

Fixpoint simplifyExpression (context : list Context)
                            (e : absExp) :=
    simplifyExp basicExpRule1 context e.
(*    @simplifyExp ev eq f t ac (fun c n e => (findVar (basicExpRule1 c n e) c)) context n e.*)

(*
 * This funciton performs some simplifications of absExp's.
 *
 * # Fixme
 * Parameters:
 *    context - a list of absExp's that are known to evaluate to non-zero values
 *    state - the total absState object in which this expression was found
 *    e - the expression to simplify
 *
 * Returned:
 *    A simplified expression.
 *)
(*Fixpoint simplifyExpression {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac)) (n : nat) (e : @absExp ev eq f) : @absExp ev eq f :=
   match e with
   | AbsConstVal v => AbsConstVal v
   | AbsVar v => findSmallerVar v context
   | AbsQVar v => subQVar v context
   | AbsFun (AbsEqualId) (e1::e2::nil) => if (beq_absExp e1 e2)
                                                 then  @AbsConstVal ev eq f (NatValue 1)
                                                 else (findVar ((@simplifyExpression ev eq f t ac context n e1)====(@simplifyExpression ev eq f t ac context n e2)) context)
   *| AbsFun (Id 8) *AbsRInclude* (element::tree::nil) => 
                     match ((simplifyExpression context state element),
                            (simplifyExpression context state tree)) with
                     | (AbsPlus base (AbsNatVal offs),t) =>
                       match findMember base context with
                       | Some tree => if ble_nat s1 offs then AbsRInclude (AbsPlus base (AbsNatVal offs)) r size fields h
                                               else if beq_absExp r1 root then AbsNatVal 1 else AbsNatVal 0
                       | None => if hasCell state (AbsPlus base (AbsNatVal offs)) then AbsNatVal 0
                                 else AbsRInclude (AbsPlus base (AbsNatVal offs)) r size fields h
                       end
                     | (e,r,h) => if hasCell state e then AbsNatVal 0 else AbsRInclude e r size fields h
                     end*
   | AbsFun (AbsImplyId) (p::q::nil) =>
                     match (@simplifyExpression ev eq f t ac context n p) with
                     | x => (findVar (x-->>(@simplifyExpression ev eq f t ac ((buildExpressionContext x false)++context) n q)) context)
                     end
   | AbsFun (AbsNotId) (p::nil) => match p with
                 | AbsFun (AbsAndId) l => (AbsFun (AbsOrId) (map (fun x => (~~(@simplifyExpression ev eq f t ac context n x))) l))
                 | AbsFun (AbsOrId) l => (AbsFun (AbsAndId) (map (fun x => (~~(@simplifyExpression ev eq f t ac context n x))) l))
                 | AbsFun (AbsNotId) (x::nil) => x
                 | _ => (findVar (~~(@simplifyExpression ev eq f t ac context n p)) context)
                 end
   | AbsFun (AbsAndId) (p::q::nil) =>
                 match @simplifyExpression ev eq f t ac ((buildExpressionContext q false)++context) n p with
                 | #0 => #0
                 | #x => @simplifyExpression ev eq f t ac context n q
                 | x => match @simplifyExpression ev eq f t ac ((buildExpressionContext x false)++context) n q with
                        | #0 => #0
                        | y => (findVar (x //\\ y) context)
                        end
                 end
   | AbsFun (AbsOrId) (p::q::nil) =>
                 match (@simplifyExpression ev eq f t ac ((buildExpressionContext q true)++context) n p) with
                 | #0 => @simplifyExpression ev eq f t ac context n q
                 | #x => #x
                 | x => match @simplifyExpression ev eq f t ac ((buildExpressionContext x true)++context) n q with
                        | #0 => p
                        | y => (findVar (x \\// y) context)
                        end
                 end
   | AbsFun (AbsIteId) (p::q::r::nil) => match (@simplifyExpression ev eq f t ac context n p) with
                     | AbsConstVal (NatValue x) => if beq_nat x 0
                                        then (@simplifyExpression ev eq f t ac context n r)
                                        else (@simplifyExpression ev eq f t ac context n q)
                     | x           => (findVar (AbsFun (AbsIteId) (x::(@simplifyExpression ev eq f t ac ((buildExpressionContext x false)++context) n q)::(@simplifyExpression ev eq f t ac ((buildExpressionContext x true)++context) n r)::nil)) context)
                     end
   | AbsFun (AbsNthId) ((AbsFun (AbsListId) l)::(AbsConstVal x)::nil) =>
                   match x with
                   | NatValue n => nth n l (@AbsConstVal ev eq f NoValue)
                   | _ =>  (@AbsConstVal ev eq f NoValue)
                   end
   | AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil) =>
                   if beq_absExp ff f' then
                       AbsFun (AbsListId)
                       ((@simplifyExpression ev eq f t ac context n ff)::
                        (map (@simplifyExpression ev eq f t ac context n) r))
                   else
                       match findDomain n context with
                       | Some d => if allPresent r d context then if beq_absExp f' (AbsQVar (n-1)) then
                                         (AbsFun (AbsFindId) (d::(@simplifyExpression ev eq f t ac context n f')::nil))
                                     else
                                       (findVar (AbsFun (AbsFindId)
                                           ((AbsFun (AbsListId)
                                                ((@simplifyExpression ev eq f t ac context n ff)::
                                                 (map (@simplifyExpression ev eq f t ac context n) r)))::
                                           (@simplifyExpression ev eq f t ac context n f')::nil)) context)
                                     else
                                       (findVar (AbsFun (AbsFindId)
                                           ((AbsFun (AbsListId)
                                                ((@simplifyExpression ev eq f t ac context n ff)::
                                                 (map (@simplifyExpression ev eq f t ac context n) r)))::
                                           (@simplifyExpression ev eq f t ac context n f')::nil)) context)
                       | None =>
                           (findVar (AbsFun (AbsFindId)
                               ((AbsFun (AbsListId)
                                    ((@simplifyExpression ev eq f t ac context n ff)::
                                     (map (@simplifyExpression ev eq f t ac context n) r)))::
                               (@simplifyExpression ev eq f t ac context n f')::nil)) context)
                       end
   | AbsFun (AbsRangeSetId) ((AbsVar x)::nil) => (AbsConstVal (ListValue nil))
   | AbsFun (AbsRangeSetId) ((AbsConstVal (ListValue nil))::nil) => (AbsConstVal (ListValue nil))
   | AbsFun i l => findVar (AbsFun i (map (@simplifyExpression ev eq f t ac context n) l)) context
   end.*)

Fixpoint eliminatedQuantVar (v : nat) (s : absState) : bool :=
   match s with
   | AbsStar x y => if eliminatedQuantVar v x then eliminatedQuantVar v y
                    else false
   | [v(n)====e] => if beq_nat n v then (if noSmallerQuantVars n e then true else false) else
                       (if hasVnExp e v then false else true)
   | [e====v(n)] => if beq_nat n v then (if noSmallerQuantVars n e then true else false) else
                       (if hasVnExp e v then false else true)
   | x => if hasVnState x v then false else true
   end.

(*Inductive simplifyExists {ev} {eq} {f} {t} {ac} : nat -> @absState ev eq f t ac -> @absState ev eq f t ac -> Prop :=
  | SEEliminate : forall n p e,
                  hasVnState p n=false ->
                  simplifyExists n (AbsExists e p) (removeStateVar n p)
  | SEEliminateT : forall n p,
                   hasVnState p n=false ->
                   simplifyExists n (AbsExistsT p) (removeStateVar n p)
  | SEEliminateQuantT : forall n p p',
                        substQuant n p p' ->
                        simplifyExists n (AbsExistsT p) (AbsExistsT p')
  | SEEliminateQuant : forall n p p' e,
                       substQuant n p p' ->
                       simplifyExists n (AbsExists e p) (AbsExists e p').
  *| SESplitNat : forall p p1 p2,
                 separateV0components p p1 p2 ->
                 ~(empty_state p2) ->
                 simplifyExists (AbsExists AbsNat p) ((AbsExists AbsNat p1) ** (instantiateNatState nil p2 0))*
  *| SESplitHeap : forall p p1 p2,
                  separateV0components p p1 p2 ->
                  ~(empty_state p2) ->
                  simplifyExists (AbsExists AbsHeap p) ((AbsExists AbsHeap p1) ** (instantiateHeapState nil p2 empty_heap)).*

Ltac solveSimplifyExists :=
    solve [(eapply SEEliminate;simpl;reflexivity) |
           (eapply SEEliminateT;simpl;reflexivity) |
           (eapply SEEliminateQuantT;solveEliminateQuant) |
           (eapply SEEliminateQuant;solveEliminateQuant) ].

Ltac solveSimplifyExistsPPP :=
    solve [(eapply SEEliminate;simpl;reflexivity) |
           (eapply SEEliminateT;simpl;reflexivity) ].
*)

Fixpoint reduceFieldRef (n : nat ) (e : absExp) : option (absExp * list absExp) :=
    match e with
    | AbsFun (AbsFindId) ((AbsFun (AbsListId) (f::l))::(AbsQVar x)::nil) =>
          if beq_nat x n then
              Some (AbsFun (AbsFindId) ((AbsQVar (S n))::(AbsQVar x)::nil),l)
          else
              None
    | AbsFun i l => match (fix go l := match l with
                                       | (ff::r) => match reduceFieldRef n ff with
                                                   | Some (a,b) => Some ((a::r),b)
                                                   | None => match go r with
                                                             | Some (a,b) => Some (ff::a,b)
                                                             | None => None
                                                             end
                                                   end
                                       | nil => None
                                       end) l with
                    | Some (a,b) => Some (AbsFun i a,b)
                    | None => None
                    end
    | x => None
    end.

Fixpoint pickAssignment (n : nat) (s : absState) : option (absState * absExp) :=
  match s with
  | AbsStar l r => match pickAssignment n l with
                   | Some (s',e) => Some ((AbsStar s' r),e)
                   | None => match pickAssignment n r with
                             | Some (s',e) => Some ((AbsStar l s'),e)
                             | None => None
                             end
                   end
  | AbsMagicWand l r => match pickAssignment n l with
                        | Some (s',e) => Some ((AbsMagicWand s' r),e)
                        | None => None
                        end
  | AbsExists l s => match pickAssignment (S n) s with
                       | Some (s',e) => Some ((AbsExists l s'),(removeExpVar 0 e))
                       | None => None
                       end
  | AbsExistsT s => match pickAssignment (S n) s with
                    | Some (s',e) => Some ((AbsExistsT s'),(removeExpVar 0 e))
                    | None => None
                    end
  | [v(x)====e] => if beq_nat x n then if noSmallerQuantVars x e then Some (AbsEmpty,e) else None else
            match e with
            | v(y) => if beq_nat y n then if ble_nat y x then Some (AbsEmpty,v(x)) else None else None
            | _ => None
            end
  | [e====v(x)] => if beq_nat x n then if noSmallerQuantVars x e then Some (AbsEmpty,e) else None else None
  | _ => None
  end.

Fixpoint pickC (x : absExp) (context : list Context) : bool :=
  match context with
  | nil => false
  | ((StateComponent (l |-> f))::r) => if beq_absExp x f then true else pickC x r
  | (_::r) => pickC x r
  end.

Fixpoint pickPred (x : absExp) (context : list Context) : bool :=
  match context with
  | nil => false
  | ((StateComponent ([p]))::r) => if beq_absExp x p then true else pickPred x r
  | ((NonZeroExpression p)::r) => if beq_absExp x p then true else pickPred x r
  | (_::r) => pickPred x r
  end.

Definition unfoldAll (v : absExp) (s : absState) (n : nat) :=
                              match v with
                              | (AbsFun (AbsListId) (ff::l)) =>
                                       fold_left (fun x y => (AbsStar x y))
                                                 (map (fun x => (AbsAll (TreeRecords(x)) s)) l)
                                                 (removeStateVar 0 (replaceStateVar 0 (addExpVar 0 ff) s))
                              | v' => AbsAll (TreeRecords(v')) s
                              end.

Definition unfoldExists (v : absExp) (s : absState) (n : nat) :=
                              match v with
                              | (AbsFun (AbsListId) (ff::l)) =>
                                       fold_left (fun x y => (AbsOrStar x y))
                                                 (map (fun x => (AbsExists (TreeRecords(x)) s)) l)
                                                 (removeStateVar 0 (replaceStateVar 0 (addExpVar 0 ff) s))
                              | v' => AbsExists (TreeRecords(v')) s
                              end.

Definition equalsNil x := x====(@AbsConstVal (ListValue nil)).

Fixpoint simplifySt
                    (erule : (list Context)
                              -> absExp -> absExp)
                    (rule : list Context -> absState ->
                            absState)
                    (context : list Context)
                    (s : absState) : absState :=
    rule context
       (match s with
        | AbsStar l r => match simplifySt erule rule ((buildStateContext r)++context) l with
                         | ll => AbsStar ll (simplifySt erule rule ((buildStateContext ll)++context) r)
                         end
        | AbsOrStar l r => match simplifySt erule rule ((buildNegStateContext r)++context) l with
                         | ll => AbsOrStar ll (simplifySt erule rule ((buildNegStateContext ll)++context) r)
                         end
        | AbsExistsT s => AbsExistsT (simplifySt erule rule (enterQuant context) s)
        | AbsExists l s => AbsExists (simplifyExp erule context l)
                                     (simplifySt erule rule ((Domain 0 (addExpVar 0 l))::(enterQuant context)) s)
        | AbsAll l s => AbsAll (simplifyExp erule context l)
                               (simplifySt erule rule ((Domain 0 (addExpVar 0 l))::(enterAll l context)) s)
        | AbsEach l s => AbsEach (simplifyExp erule context l)
                                 (simplifySt erule rule ((Domain 0 (addExpVar 0 l))::(enterQuant context)) s)
        | AbsLeaf f l => AbsLeaf f (map (simplifyExp erule context) l)
        | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (simplifyExp erule context e1)
                                          (simplifyExp erule ((Domain 0 e1)::(enterQuant context)) e2)
                                          (simplifyExp erule context e3)
        | AbsUpdateVar s v e => AbsUpdateVar (simplifySt erule rule context s) v (simplifyExp erule context e)
        | AbsUpdateWithLoc s v e => AbsUpdateWithLoc (simplifySt erule rule context s) v (simplifyExp erule context e)
        | AbsUpdateLoc s l e => AbsUpdateLoc (simplifySt erule rule context s) (simplifyExp erule context l) (simplifyExp erule context e)
        | AbsUpdState s s1 s2 => AbsUpdState (simplifySt erule rule context s) (simplifySt erule rule context s1) (simplifySt erule rule context s2)
        | AbsMagicWand s1 s2 => AbsMagicWand (simplifySt erule rule context s1) (simplifySt erule rule context s2)
        | x => x
        end).

Fixpoint srule (context : list Context)
                                      (s : absState) : absState :=
     match s return absState with
     (*| AbsStar l r => match l with
                      | ([#x]) => if beq_nat x 0 then ([#0]) else r
                      | AbsEmpty => r
                      | AbsExistsT ll => match r with
                                         | AbsEmpty => AbsExistsT ll
                                         | rr => AbsExistsT (AbsStar ll (addStateVar n rr))
                                         end
                      | AbsExists l ll => match r with
                                         | AbsEmpty => AbsExists l ll
                                         | rr => AbsExists l (AbsStar ll (addStateVar n rr))
                                         end
                      | ll => match r with
                              | ([#x]) => if beq_nat x 0 then ([#0]) else l
                              | AbsEmpty => ll
                              | AbsExistsT rr => AbsExistsT (AbsStar (addStateVar n ll) rr)
                              | AbsExists l rr => AbsExists l (AbsStar (addStateVar n ll) rr)
                              | rr => AbsStar ll rr
                              end
                      end
     | AbsMagicWand l r => match l with
                      | ([#x]) => if beq_nat x 0 then ([#0]) else r
                      | AbsEmpty => r
                      | AbsExistsT ll => match r with
                                         | AbsEmpty => AbsExistsT ll
                                         | rr => AbsExistsT (AbsMagicWand ll (addStateVar n rr))
                                         end
                      | AbsExists l ll => match r with
                                         | AbsEmpty => AbsExists l ll
                                         | rr => AbsExists l (AbsMagicWand ll (addStateVar n rr))
                                         end
                      | ll => match r with
                              | ([#x]) => if beq_nat x 0 then ([#0]) else l
                              | AbsEmpty => ll
                              | AbsExistsT rr => AbsExistsT (AbsMagicWand (addStateVar n ll) rr)
                              | AbsExists l rr => AbsExists l (AbsMagicWand (addStateVar n ll) rr)
                              | rr => AbsMagicWand ll rr
                              end
                      end*)
     | AbsExistsT s => match pickAssignment 0 s return absState with
                       | Some (s',e) => removeStateVar 0 (substState s' 0 e)
                       | None => if hasVnState s 0 then AbsExistsT s else removeStateVar 0 s
                       end
     | AbsExists(TreeRecords(v)) s => if pickC v context then [#0]
                                      else match ((TreeRecords(v)),s) return absState with
                                           | ((TreeRecords(e)),s') => unfoldExists e s' 0
                                           | (e,s') => AbsExists e s'
                                           end
     | AbsExists(AbsConstVal (ListValue nil)) s => AbsNone
     | AbsExists(AbsConstVal (NatValue _)) s => AbsNone
     | AbsExists l s =>match pickAssignment 0 s return absState with
                       | Some (s',e) => removeStateVar 0 (substState s' 0 e)
                       | None =>  if hasVnState s 0 then AbsExists l s else removeStateVar 0 s
                       end
     | AbsAll(AbsConstVal (ListValue nil)) s => AbsEmpty
     | AbsAll(AbsConstVal (NatValue _)) s => AbsEmpty
     | AbsAll(TreeRecords(v)) s => if pickC v context then AbsEmpty
                                   else match ((TreeRecords(v)),s) return absState with
                                        | (e,(AbsStar l r)) => (AbsStar (AbsAll e l) (AbsAll e r))
                                        | ((TreeRecords(e)),s') => unfoldAll e s' 0
                                        | (e,s') => AbsAll e s'
                                        end
     | AbsAll v s => match v,s return absState with
                     | v',AbsStar l r => AbsStar (AbsAll v' l) (AbsAll v' r)
                     | v',s' => AbsAll v' s'
                     end
     | AbsStar (AbsUpdateVar l v e) r => if hasVarState r v then
                                             match r return absState with
                                             | AbsUpdateVar rr vv ee =>
                                               if hasVarState l vv then
                                                   s
                                               else
                                                   AbsUpdateVar (AbsStar (AbsUpdateVar l v e) rr) vv ee
                                             | x => AbsStar (AbsUpdateVar l v e) r
                                             end
                                         else
                                             AbsUpdateVar (AbsStar l r) v e
     | (AbsStar l (AbsUpdateVar r v e)) => if hasVarState l v then
                                               s
                                           else
                                               AbsUpdateVar (AbsStar l r) v e
     (*| AbsMagicWand (AbsUpdateVar l v e) r => if hasVarState r v then
                                             match r return @absState ev eq f t ac with
                                             | AbsUpdateVar rr vv ee =>
                                               if hasVarState l vv then
                                                   s
                                               else
                                                   AbsUpdateVar (AbsMagicWand (AbsUpdateVar l v e) rr) vv ee
                                             | x => AbsMagicWand (AbsUpdateVar l v e) r
                                             end
                                         else
                                             AbsUpdateVar (AbsMagicWand l r) v e
     | (AbsMagicWand l (AbsUpdateVar r v e)) => if hasVarState l v then
                                               s
                                           else
                                               AbsUpdateVar (AbsMagicWand l r) v e*)
     (*| AbsMagicWand (AbsUpdateWithLoc l v e) r => if hasVarState r v then
                                             match r return @absState ev eq f t ac with
                                             | AbsUpdateWithLoc rr vv ee =>
                                               if hasVarState l vv then
                                                   s
                                               else
                                                   AbsUpdateWithLoc (AbsMagicWand (AbsUpdateWithLoc l v e) rr) vv ee
                                             | x => AbsMagicWand (AbsUpdateWithLoc l v e) r
                                             end
                                         else
                                             AbsUpdateWithLoc (AbsMagicWand l r) v e
     | (AbsMagicWand l (AbsUpdateWithLoc r v e)) => if hasVarState l v then
                                               s
                                           else
                                               AbsUpdateWithLoc (AbsMagicWand l r) v e*)
     | [(a //\\ b)] => AbsStar ([a]) ([b])
     | [(~~a \\// ~~b)] => if pickPred a context then
                             [~~b]
                          else if pickPred b context then
                             [~~a]
                          else
                             [~~a] *\/* [~~b]
     | [(a \\// ~~b)] => if pickPred (~~a) context then
                             [~~b]
                         else if pickPred b context then
                             [a]
                         else
                             [a] *\/* [~~b]
     | [(~~a \\// b)] => if pickPred (a) context then
                             [b]
                         else if pickPred (~~b) context then
                             [~~a]
                         else
                             [~~a] *\/* [b]
     | [(a \\// b)] => if pickPred (~~a) context then
                             [b]
                         else if pickPred (~~b) context then
                             [a]
                         else
                             [a] *\/* [b]
     | (x *\/* AbsNone) => x
     | (x ** AbsEmpty) => x
     | (AbsEmpty ** x) => x
     | (AbsNone *\/* x) => x
     | [(#n)] => if beq_nat n 0 then AbsNone else AbsEmpty
     | AbsLeaf (AbsTreeId) (#0::v::_) => [equalsNil v]
     | [x ==== (#0)] => if hasNonZero context x then AbsNone else [x ==== (#0)]
     | [(#0) ==== x] => if hasNonZero context x then AbsNone else [(#0) ==== x]
     | x => x
     end.

Fixpoint existsrule (context : list Context)
                                      (s : absState) : absState :=
     match s return absState with
     | AbsStar l r => match l with
                      | ([#x]) => if beq_nat x 0 then ([#0]) else r
                      | AbsEmpty => r
                      | AbsExistsT ll => match r with
                                         | AbsEmpty => AbsExistsT ll
                                         | rr => AbsExistsT (AbsStar ll (addStateVar 0 rr))
                                         end
                      | AbsExists l ll => match r with
                                         | AbsEmpty => AbsExists l ll
                                         | rr => AbsExists l (AbsStar ll (addStateVar 0 rr))
                                         end
                      | ll => match r with
                              | AbsExistsT rr => AbsExistsT (AbsStar (addStateVar 0 ll) rr)
                              | AbsExists l rr => AbsExists l (AbsStar (addStateVar 0 ll) rr)
                              | rr => AbsStar ll rr
                              end
                      end
     | AbsMagicWand l r => match l with
                      | AbsEmpty => r
                      | AbsExistsT ll => match r with
                                         | AbsEmpty => AbsExistsT ll
                                         | rr => AbsExistsT (AbsMagicWand ll (addStateVar 0 rr))
                                         end
                      | AbsExists l ll => match r with
                                         | AbsEmpty => AbsExists l ll
                                         | rr => AbsExists l (AbsMagicWand ll (addStateVar 0 rr))
                                         end
                      | ll => match r with
                              | ([#x]) => if beq_nat x 0 then ([#0]) else l
                              (*| AbsExistsT rr => AbsExistsT (AbsMagicWand (addStateVar 0 ll) rr)
                              | AbsExists l rr => AbsExists l (AbsMagicWand (addStateVar 0 ll) rr)*)
                              | rr => AbsMagicWand ll rr
                              end
                      end
     | AbsUpdateVar (AbsExistsT s) v e => (AbsExistsT (AbsUpdateVar s v (addExpVar 0 e)))
     | AbsUpdateLoc (AbsExistsT s) v e => (AbsExistsT (AbsUpdateLoc s v (addExpVar 0 e)))
     | AbsUpdateWithLoc (AbsExistsT s) v e => (AbsExistsT (AbsUpdateWithLoc s v (addExpVar 0 e)))
     | x => x
     end.

Fixpoint srule2 (context : list Context )
                                      (s : absState) : absState :=
     match s return absState with
     | AbsStar (AbsUpdateVar l v e) r => if hasVarState r v then
                                             match r return absState with
                                             | AbsUpdateVar rr vv ee =>
                                               if hasVarState l vv then
                                                   s
                                               else
                                                   AbsUpdateVar (AbsStar (AbsUpdateVar l v e) rr) vv ee
                                             | x => AbsStar (AbsUpdateVar l v e) r
                                             end
                                         else
                                             AbsUpdateVar (AbsStar l r) v e
     | (AbsStar l (AbsUpdateVar r v e)) => if hasVarState l v then
                                               s
                                           else
                                               AbsUpdateVar (AbsStar l r) v e
     | x => x
     end.

Fixpoint simplifyState (context : list Context) (s : absState) : absState :=
     simplifySt (fun c e => (basicExpRule1 c e)) srule context s.

Fixpoint propagateExists (context : list Context) (s : absState) : absState :=
     simplifySt (fun c e => (basicExpRule1 c e)) existsrule context s.

(*Fixpoint simplifyState {ev} {eq} {f} {t} {ac} (n : nat) (context : list (@Context ev eq f t ac)) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
  match s return @absState ev eq f t ac with
  | AbsStar l r => match simplifyState n ((buildStateContext r)++context) l with
                   | AbsEmpty => simplifyState n context r
                   | AbsExistsT ll => match simplifyState n ((buildStateContext (AbsExistsT ll))++context) r return @absState ev eq f t ac with
                                      | AbsEmpty => AbsExistsT ll
                                      | rr => AbsExistsT (AbsStar ll (addStateVar n rr))
                                      end
                   | AbsExists l ll => match simplifyState n ((buildStateContext (AbsExistsT ll))++context) r return @absState ev eq f t ac with
                                         | AbsEmpty => AbsExists l ll
                                         | rr => AbsExists l (AbsStar ll (addStateVar n rr))
                                         end
                   | ll => match simplifyState n ((buildStateContext ll)++context) r return @absState ev eq f t ac with
                           | AbsEmpty => ll
                           | AbsExistsT rr => AbsExistsT (AbsStar (addStateVar n ll) rr)
                           | AbsExists l rr => AbsExists l (AbsStar (addStateVar n ll) rr)
                           | rr => AbsStar ll rr
                           end
                   end
  | AbsExistsT s => match simplifyState (S n) context s with
                    | ss => match pickAssignment n ss return @absState ev eq f t ac with
                            | Some (s',e) => if hasVnState s' n then AbsExistsT ss else removeStateVar n s'
                            | None => if hasVnState ss n then AbsExistsT ss else removeStateVar n ss
                            end
                    end
  | AbsExists l s => match simplifyState (S n) ((Domain (S n) l)::context) s with
                     | ss => match pickAssignment n ss return @absState ev eq f t ac with
                                | Some (s',e) => if hasVnState s' n then AbsExists (simplifyExpression context n l) ss else removeStateVar n s'
                                | None =>  if hasVnState ss n then AbsExists (simplifyExpression context n l) ss else removeStateVar n ss
                                end
                     end
  | AbsAll(AbsConstVal (ListValue nil)) s => AbsEmpty
  | AbsAll(TreeRecords(v)) s => if pickC v context then AbsEmpty
                                else match simplifyExpression context n (TreeRecords(v)),simplifyState (S n) ((Domain (S n) (TreeRecords(v)))::context) s return @absState ev eq f t ac with
                                     | e,(AbsStar l r) => (AbsStar (AbsAll e l) (AbsAll e r))
                                     | (TreeRecords(e)),s' => unfoldAll e s' n
                                     | e,s' => AbsAll e s'
                                     end
  | AbsAll v s => match simplifyExpression context n v,simplifyState (S n) ((Domain (S n) v)::context) s return @absState ev eq f t ac with
                  | v',AbsStar l r => AbsStar (AbsAll v' l) (AbsAll v' r)
                  | v',s' => AbsAll v' s'
                  end
  | AbsEach v s => AbsEach (simplifyExpression context n v) (simplifyState (S n) ((Domain (S n) v)::context) s)
  | [ p ] => match simplifyExpression context n p return @absState ev eq f t ac with
             | (a //\\ b) => AbsStar ([a]) ([b])
             | (~~a \\// ~~b) => if pickPred a context then
                            [~~b]
                        else if pickPred b context then
                            [~~a]
                        else
                            [~~a \\// ~~b]
             | (a \\// ~~b) => if pickPred (~~a) context then
                            [~~b]
                        else if pickPred b context then
                            [a]
                        else
                            [~~a \\// ~~b]
             | (~~a \\// b) => if pickPred (a) context then
                            [b]
                        else if pickPred (~~b) context then
                            [~~a]
                        else
                            [~~a \\// b]
             | (a \\// b) => if pickPred (~~a) context then
                            [b]
                        else if pickPred (~~b) context then
                            [a]
                        else
                            [a \\// b]
             | (#n) => if beq_nat n 0 then [#n] else AbsEmpty
             | x => [x]
             end
  | AbsLeaf (AbsTreeId) (#0::v::_) => [equalsNil v]
  | AbsLeaf f l => AbsLeaf f (map (simplifyExpression context n) l)
  | x => x
  end.*)

(*
 * All of the theorems and tactics below are used to apply simplification in different
 * situates in a program proof.
 *)
Ltac simplifyState :=
    (compute; reflexivity).

Theorem simplifyEquiv1 : forall (s : absState) s' state,
    s' = simplifyState nil s ->
    realizeState s nil state ->
    realizeState s' nil state.
Proof. admit. Admitted.

Theorem propagateExistsEquiv1 : forall (s : absState) s' state b,
    s' = propagateExists nil s ->
    realizeState s b state ->
    realizeState s' b state.
Proof. admit. Admitted.

Ltac simplifyTheHyp H := eapply simplifyEquiv1 in H; [idtac | compute; reflexivity].

Definition basicSimplifyEquiv1 := simplifyEquiv1.

Theorem simplifyEquivb1 : forall (s : absState) s' b state,
    s' = simplifyState nil s ->
    realizeState s b state ->
    realizeState s' b state.
Proof. admit. Admitted.

Ltac simplifyHyp X:=
    eapply simplifyEquivb1 in X;[compute in X|simplifyState].

Theorem simplifyEquiv2 : forall (s : absState) s' state b,
    s' = simplifyState nil s ->
    realizeState s' b state -> realizeState s b state.
Proof. admit. Admitted.

Theorem propagateExistsEquiv2 : forall (s : absState) s' state b,
    s' = propagateExists nil s ->
    realizeState s' b state -> realizeState s b state.
Proof. admit. Admitted.

Ltac simplify := eapply simplifyEquiv2; compute; [reflexivity | idtac].
Ltac propagateExists := eapply propagateExistsEquiv2; compute; [reflexivity | idtac].
Ltac propagateExistsHyp H := eapply propagateExistsEquiv1 in H; [compute in H | simplifyState].

Theorem simplifyAbsEval : forall (e : absExp) e' b env,
    e' = simplifyExpression nil e ->
    absEval env b e'= absEval env b e.
Proof. admit. Admitted.

Theorem simplifyPre : forall (s : absState) s' cmd post r post',
    s' = simplifyState nil s ->
    {{ s' }} cmd {{ post return r with post'}} ->
    {{ s }} cmd {{ post return r with post'}}.
Proof. admit.
    (*unfold hoare_triple. unfold absExecute. intros.
    eapply H0. eapply simplifyEquiv1. apply H. apply H1.*)
Admitted.

Theorem tsimplifyPre : forall (s : absState) s' cmd post r post',
    {{ s' }} cmd {{ post return r with post' }} ->
    s' = simplifyState nil s ->
    {{ s }} cmd {{ post return r with post' }}.
Proof. admit.
    (*unfold hoare_triple. unfold absExecute. intros.
    eapply H. eapply simplifyEquiv1. apply H0. apply H1.*)
Admitted.

Opaque basicEval.

Ltac simp := eapply simplifyPre;[(compute;reflexivity)|idtac].
Ltac simplifyPre := repeat (progress simp).

Ltac simpBasic := eapply (simplifyPre tt)
                    ;[simplifyState|(instantiate;simpl)] || idtac.
Ltac simplifyPreBasic := repeat (progress simpBasic).

Theorem realizeStateSimplify: forall (P : absState) P' bindings s,
    P' = simplifyState nil P ->
    realizeState P' bindings s ->
    realizeState P bindings s.
Proof.
    admit.
Admitted.

Theorem mergeSimplifyLeft : forall (P1 : absState) P1' P2 P,
    P1' = simplifyState nil P1 ->
    mergeStates P1' P2 P ->
    mergeStates P1 P2 P.
Proof. (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. eapply H1. eapply simplifyEquiv1. reflexivity. apply H. intros. apply H2. apply H.*) admit.
Admitted.

Theorem mergeSimplifyRight: forall (P1 : absState) P2 P2' P,
    P2' = simplifyState nil P2 ->
    mergeStates P1 P2' P ->
    mergeStates P1 P2 P.
Proof. (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. apply H1. apply H. intros. eapply H2. eapply simplifyEquiv1.
    reflexivity. eapply H.*) admit.
Admitted.

Ltac simpleft := eapply mergeSimplifyLeft;[(compute;reflexivity)|idtac].
Ltac mergeSimplifyLeft := repeat (progress simpleft).

Ltac simpright := eapply mergeSimplifyRight;[(compute;reflexivity)|idtac].
Ltac mergeSimplifyRight := repeat (progress simpright).

Theorem mergePropagateLeft : forall (P1 : absState) P1' P2 P,
    P1' = propagateExists nil P1 ->
    mergeStates P1' P2 P ->
    mergeStates P1 P2 P.
Proof. (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. eapply H1. eapply simplifyEquiv1. reflexivity. apply H. intros. apply H2. apply H.*) admit.
Admitted.

Theorem mergePropagateRight : forall (P1 : absState) P2 P2' P,
    P2' = propagateExists nil P2 ->
    mergeStates P1 P2' P ->
    mergeStates P1 P2 P.
Proof. (*unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. apply H1. apply H. intros. eapply H2. eapply simplifyEquiv1.
    reflexivity. eapply H.*) admit.
Admitted.

Ltac propleft := eapply mergePropagateLeft;[(compute;reflexivity)|idtac].
Ltac mergePropagateExistsLeft := repeat (progress propleft).

Ltac propright := eapply mergePropagateRight;[(compute;reflexivity)|idtac].
Ltac mergePropagateExistsRight := repeat (progress propright).


Function  stripUpdateVar (s : absState) :=
    match s with
    | AbsUpdateVar ss i v =>
          match substVarState (addStateVar 0 (stripUpdateVar ss)) i v(0) with
          | Some x => [!!(i) ==== v] ** (AbsExistsT x)
          | None => AbsUpdateVar ss i v
          end
    | (a ** b) => (stripUpdateVar a) ** (stripUpdateVar b)
    | AbsExistsT x => AbsExistsT (stripUpdateVar x)
    | AbsUpdateLoc s i v => AbsUpdateLoc (stripUpdateVar s) i v
    | AbsUpdateWithLoc s i v => AbsUpdateWithLoc (stripUpdateVar s) i v
    | AbsMagicWand l r => AbsMagicWand (stripUpdateVar l) r
    | x => x
    end.

Function findCell (e : absExp) (s : absState) :=
    match s with
    | AbsStar a b => match findCell e a with
               | Some x => Some x
               | None => findCell e b
               end
    | AbsUpdateWithLoc s i v => if hasVarExp e i then None else findCell e s
    | AbsUpdateVar s i v => if hasVarExp e i then None else findCell e s
    | x |-> y => if beq_absExp x e then Some y else None
    | _ => None
    end.

Function  stripUpdateWithLoc (s : absState) :=
    match s with
    | AbsUpdateWithLoc ss i v => match findCell v ss,substVarState (addStateVar 0 (stripUpdateWithLoc ss)) i v(0) with
                                 | Some v,Some x => [!!(i) ==== v] ** (AbsExistsT x)
                                 | _,_ => AbsUpdateWithLoc (stripUpdateWithLoc ss) i v
                                 end
    | (a ** b) => (stripUpdateWithLoc a) ** (stripUpdateWithLoc b)
    | AbsExistsT x => AbsExistsT (stripUpdateWithLoc x)
    | AbsUpdateLoc s i v => AbsUpdateLoc (stripUpdateWithLoc s) i v
    | AbsUpdateVar s i v => AbsUpdateVar (stripUpdateWithLoc s) i v
    | AbsMagicWand l r => AbsMagicWand (stripUpdateWithLoc l) r
    | x => x
    end.

Theorem stripUpdateVarLeft : forall left left' right m,
    left' = stripUpdateVar left ->
    mergeStates left' right m ->
    mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarLeftp
    : forall left right m,
      mergeStates (stripUpdateVar left) right m -> mergeStates left right m.
Proof.
    admit.
Admitted.


Theorem stripUpdateWithLocLeft : forall left left' right m,
    left' = stripUpdateWithLoc left ->
    mergeStates left' right m ->
    mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocLeftp
    : forall P1 P2 P,
      mergeStates (stripUpdateWithLoc P1) P2 P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarRight : forall left right' right m,
    right' = stripUpdateVar right ->
    mergeStates left right' m ->
    mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarRightp
    : forall left right m,
      mergeStates left (stripUpdateVar right) m -> mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocRightp
    : forall P1 P2 P,
      mergeStates P1 (stripUpdateWithLoc P2) P -> mergeStates P1 P2 P.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocRight : forall left right' right m,
    right' = stripUpdateWithLoc right ->
    mergeStates left right' m ->
    mergeStates left right m.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarHyp : forall state state' b s,
    realizeState state b s ->
    state' = stripUpdateVar state ->
    realizeState state' b s.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarHypp : forall state b s,
    realizeState state b s ->
    realizeState (stripUpdateVar state) b s.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocHyp : forall state state' b s,
    realizeState state b s ->
    state' = stripUpdateWithLoc state ->
    realizeState state' b s.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocHypp : forall state b s,
    realizeState state b s ->
    realizeState (stripUpdateWithLoc state) b s.
Proof.
    admit.
Admitted.

Theorem stripUpdateVarp : forall state b s,
    realizeState (stripUpdateVar state) b s ->
    realizeState state b s.
Proof.
    admit.
Admitted.

Theorem stripUpdateWithLocp : forall state b s,
    realizeState (stripUpdateWithLoc state) b s ->
    realizeState state b s.
Proof.
    admit.
Admitted.

Theorem mergeReductionUpdateVarLeft : forall (va : id) (l : absState)
             (r : absState) (m : absState)
             (vall : absExp),
    mergeStates l r m ->
    hasVarState l va = false ->
    hasVarExp vall va = false ->
    mergeStates (AbsUpdateVar l va vall) r m.
Proof.
    admit.
Admitted.

Theorem mergeReductionUpdateVarLeft2 : forall (va : id) (l : absState)
             (r : absState) (m : absState)
             (vall : absExp),
    mergeStates l r m ->
    (forall b s, realizeState (AbsUpdateVar l va vall) b s -> realizeState l b s) ->
    mergeStates (AbsUpdateVar l va vall) r m.
Proof.
    admit.
Admitted.

Theorem mergeReductionUpdateVarLeft3 : forall (va : id) (l : absState)
             (r : absState) (m : absState)
             (vall : absExp),
    mergeStates l r m ->
    (forall s b, realizeState l b s -> (NatValue (fst s va))=absEval (fst s) b vall) ->
    mergeStates (AbsUpdateVar l va vall) r m.
Proof.
    admit.
Admitted.

Theorem mergeReductionUpdateWithLocLeft : forall (va : id) (l : absState)
             (r : absState) (m : absState)
             (vall : absExp),
    mergeStates l r m ->
    hasVarState l va = false ->
    hasVarExp vall va = false ->
    mergeStates (AbsUpdateWithLoc l va vall) r m.
Proof.
    admit.
Admitted.

Theorem mergeReductionUpdateWithLocRight : forall (va : id) (l : absState)
             (r : absState) (m : absState)
             (vall : absExp),
    mergeStates l r m ->
    hasVarState r va = false ->
    hasVarExp vall va = false ->
    mergeStates l (AbsUpdateWithLoc r va vall) m.
Proof.
    admit.
Admitted.

Theorem mergeImplies : forall (s1 : absState) s2 m1 m2,
    mergeStates s1 s2 m1 ->
    (forall s b, realizeState m1 b s -> realizeState m2 b s) ->
    mergeStates s1 s2 m2.
Proof.
    admit.
Admitted.

Theorem mergeSame : forall (s : absState),
    mergeStates s s s.
Proof.
    admit.
Admitted.

Theorem removeCondLeftLeft : forall (c : absExp) (s1 : absState) (s2 : absState) (m : absState),
    mergeStates s1 s2 m ->
    mergeStates (AbsStar ([c]) s1) s2 m.
Proof.
    admit.
Admitted.
    
Theorem removeCondRightLeft : forall (c : absExp) (s1 : absState) (s2 : absState) (m : absState),
    mergeStates s1 s2 m ->
    mergeStates s1 (AbsStar ([c]) s2) m.
Proof.
    admit.
Admitted.

Fixpoint updateCell (p : absState) (loc : absExp) (v : absExp) :=
    match p with
    | AbsStar l r => match updateCell l loc v with
                     | Some ll => Some (AbsStar ll r)
                     | None => match updateCell r loc v with
                               | Some rr => Some (AbsStar l rr)
                               | None => None
                               end
                     end
    | AbsExistsT e => match updateCell e (addExpVar 0 loc) (addExpVar 0 v) with
                      | Some l => Some (AbsExistsT l)
                      | None => None
                      end
    | AbsExists ee e => match updateCell e (addExpVar 0 loc) (addExpVar 0 v) with
                        | Some l => Some (AbsExists ee l)
                        | None => None
                        end
    | (l |-> _) => if beq_absExp l loc then Some (l |-> v) else None
    | _ => None
    end.

Fixpoint removeUpdateLoc (s : absState) :=
    match s with
    | AbsExistsT e => match removeUpdateLoc e with
                      | Some x => Some (AbsExistsT x)
                      | None => None
                      end
    | AbsExists e s => match removeUpdateLoc s with
                       | Some x => Some (AbsExists e x)
                       | None => None
                       end
    | AbsStar l r => match removeUpdateLoc l with
                       | Some x => Some (AbsStar x r)
                       | None => match removeUpdateLoc r with
                                 | Some x => Some (AbsStar l x)
                                 | None => None
                                 end
                       end
    | AbsUpdateVar s v e => match removeUpdateLoc s with
                            | Some x => Some (AbsUpdateVar x v e)
                            | None => None
                          end
    | AbsUpdateWithLoc s v e => match removeUpdateLoc s with
                                | Some x => Some (AbsUpdateWithLoc x v e)
                                | None => None
                                end
    | AbsMagicWand l r => match removeUpdateLoc l with
                          | Some x => Some (AbsMagicWand x r)
                          | None => match removeUpdateLoc r with
                                    | Some x => Some (AbsMagicWand l x)
                                    | None => None
                                    end
                          end
    | AbsUpdateLoc s v e => match updateCell s v e with
                            | Some x => Some x
                            | None => match removeUpdateLoc s with
                                      | Some x => Some (AbsUpdateLoc x v e)
                                      | None => None
                                      end
                            end
    | x => None
    end.

Theorem removeUpdateLocHyp : forall state b s x,
    Some x = removeUpdateLoc state ->
    realizeState state b s -> realizeState x b s.
Proof. admit. Admitted.

Theorem removeUpdateLocThm : forall state b s x,
    Some x = removeUpdateLoc state ->
    realizeState x b s -> realizeState state b s.
Proof. admit. Admitted.

Theorem removeUpdateLocLeft : forall left left' right merge,
    Some left' = removeUpdateLoc left ->
    mergeStates left' right merge -> mergeStates left right merge.
Proof. admit. Admitted.

Theorem removeUpdateLocRight : forall left right' right merge,
    Some right' = removeUpdateLoc right ->
    mergeStates left right' merge -> mergeStates left right merge.
Proof. admit. Admitted.

Fixpoint findAssignments (v : id) (s : absState) : list absExp :=
  match s with
  | AbsStar l r => (findAssignments v l)++(findAssignments v r)
  | [(!!vv)====(!!vvv)] => if beq_id vv v then (!!vvv)::nil else
                           if beq_id vvv v then (!!vv)::nil else nil
  | [(!!vv)====e] => if beq_id vv v then e::nil else nil
  | [e====(!!vv)] => if beq_id vv v then e::nil else nil
  | _ => nil
  end.

Fixpoint replaceExp (p : absExp) (r : absExp) (t : absExp) :=
    if beq_absExp p t then r
    else match t with
         | AbsFun i l => AbsFun i (map (replaceExp p r) l)
         | x => x
         end.

Fixpoint replaceState (p : absExp) (r : absExp) (s : absState) : option absState :=
   match s with
    | AbsStar s1 s2 => match replaceState p r s1,replaceState p r s2 with
                       | Some a,Some b => Some (AbsStar a b)
                       | _,_ => None
                       end
    | AbsOrStar s1 s2 => match replaceState p r s1,replaceState p r s2 with
                         | Some a,Some b => Some (AbsOrStar a b)
                         | _,_ => None
                         end
    | AbsExistsT s => match replaceState (addExpVar 0 p) (addExpVar 0 r) s with
                      | Some x => Some (AbsExistsT x)
                      | _ => None
                      end
    | AbsExists e s => match replaceState (addExpVar 0 p) (addExpVar 0 r) s with
                       | Some x => Some (AbsExists (replaceExp p r e) x)
                       | None => None
                       end
    | AbsAll e s => match replaceState (addExpVar 0 p) (addExpVar 0 r) s with
                    | Some x => Some (AbsAll (replaceExp p r e) x)
                    | None => None
                    end
    | AbsEach e s => match replaceState (addExpVar 0 p) (addExpVar 0 r) s with
                     | Some x => Some (AbsEach (replaceExp p r e) x)
                     | None => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsAny => Some AbsAny
    | AbsNone => Some AbsNone
    | AbsLeaf i l => Some (AbsLeaf i (map (fun x => replaceExp p r x) l))
    | AbsAccumulate id e1 e2 e3 => Some (AbsAccumulate id (replaceExp p r e1) (replaceExp p r e2) (replaceExp p r e3))
    | AbsMagicWand s1 s2 => match replaceState p r s1,replaceState p r s2 with
                            | Some a,Some b => Some (AbsMagicWand a b)
                            | _,_ => None
                            end
    | AbsUpdateVar s v vall => if hasVarExp p v then None
                               else if hasVarExp r v then None
                               else match replaceState p r s with
                                    | Some x => Some (AbsUpdateVar x v (replaceExp p r vall))
                                    | _ => None
                                    end
    | AbsUpdateWithLoc s v vall => if hasVarExp p v then None
                                   else if hasVarExp p v then None
                                   else match replaceState p r s with
                                        | Some x => Some (AbsUpdateWithLoc x v (replaceExp p r vall))
                                        | _ => None
                                        end
    | AbsUpdateLoc s v vall => match (replaceState p r s),(replaceExp p r v),(replaceExp p r vall) with
                               | Some a,b,c => Some (AbsUpdateLoc a b c)
                               | _,_,_ => None
                               end
    | AbsUpdState s1 s2 s3 =>  match (replaceState p r s1),(replaceState p r s2),(replaceState p r s3) with
                               | Some a,Some b,Some c => Some (AbsUpdState a b c)
                               | _,_,_ => None
                               end
    | AbsClosure s l => Some (AbsClosure s (map (replaceExp p r) l))
   end.

Fixpoint listReplace (v : id) (r : list absExp) (e : absExp)  : option absExp :=
    match r with
    | (a::b) => if beq_absExp e a then Some (!!v) else listReplace v b e
    | nil => None
    end.

Fixpoint findAssignmentsExp (v: id) (r : list absExp) (e: absExp): absExp :=
    (*match r with
    | (_::_::nil) => v(123)
    | _ =>*)
    match e with
    | AbsFun id l => match listReplace v r e with
                     | Some x => x
                     | None => AbsFun id (map (findAssignmentsExp v r) l)
                     end
    | x => match listReplace v r x with Some y => y | None => e end
    end (*end*).

Fixpoint findAssignmentsState (v : id) (r : list absExp) (s : absState) : option absState :=
    match s with
    | AbsStar s1 s2 => match findAssignmentsState v r s1,findAssignmentsState v r s2 with
                       | Some a,Some b => Some (AbsStar a b)
                       | _,_ => None
                       end
    | AbsOrStar s1 s2 => match findAssignmentsState v r s1,findAssignmentsState v r s2 with
                         | Some a,Some b => Some (AbsOrStar a b)
                         | _,_ => None
                         end
    | AbsExistsT s => match findAssignmentsState v (map (addExpVar 0) r) s with
                      | Some x => Some (AbsExistsT x)
                      | _ => None
                      end
    | AbsExists e s => match findAssignmentsState v (map (addExpVar 0) r) s with
                       | Some x => Some (AbsExists (findAssignmentsExp v r e) x)
                       | None => None
                       end
    | AbsAll e s => match findAssignmentsState v (map (addExpVar 0) r) s with
                    | Some x => Some (AbsAll (findAssignmentsExp v r e) x)
                    | None => None
                    end
    | AbsEach e s => match findAssignmentsState v (map (addExpVar 0) r) s with
                     | Some x => Some (AbsEach (findAssignmentsExp v r e) x)
                     | None => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsAny => Some AbsAny
    | AbsNone => Some AbsNone
    | ([(!!vv)====e]) => if beq_id vv v then Some ([(!!vv)====e])
                         else Some ([findAssignmentsExp v r ((!!v)====e)])
    | ([e====(!!vv)]) => if beq_id vv v then Some ([(!!vv)====e])
                         else Some ([findAssignmentsExp v r ((!!v)====e)])
    | AbsLeaf i l => Some (AbsLeaf i (map (fun x => findAssignmentsExp v r x) l))
    | AbsAccumulate id e1 e2 e3 => Some (AbsAccumulate id (findAssignmentsExp v r e1) (findAssignmentsExp v r e2) (findAssignmentsExp v r e3))
    | AbsMagicWand s1 s2 => match findAssignmentsState v r s1,findAssignmentsState v r s2 with
                            | Some a,Some b => Some (AbsMagicWand a b)
                            | _,_ => None
                            end
    | AbsUpdateVar s vv vall => if beq_id vv v then None
                               else if hasVarExpList r vv then None
                               else match findAssignmentsState v r s with
                                    | Some x => Some (AbsUpdateVar x v (findAssignmentsExp v r vall))
                                    | _ => None
                                    end
    | AbsUpdateWithLoc s vv vall => if beq_id vv v then None
                                   else if hasVarExpList r vv then None
                                   else match findAssignmentsState v r s with
                                        | Some x => Some (AbsUpdateWithLoc x v (findAssignmentsExp v r vall))
                                        | _ => None
                                        end
    | AbsUpdateLoc s vv vall => match (findAssignmentsState v r s),(findAssignmentsExp v r vv),(findAssignmentsExp v r vall) with
                               | Some a,b,c => Some (AbsUpdateLoc a b c)
                               | _,_,_ => None
                               end
    | AbsUpdState s1 s2 s3 =>  match (findAssignmentsState v r s1),(findAssignmentsState v r s2),(findAssignmentsState v r s3) with
                               | Some a,Some b,Some c => Some (AbsUpdState a b c)
                               | _,_,_ => None
                               end
    | AbsClosure s l => Some (AbsClosure s (map (findAssignmentsExp v r) l))
   end.

Fixpoint normalize (v : id) (s : absState) :=
    match s with
    | AbsExistsT s => AbsExistsT (normalize v s)
    | AbsUpdateVar s i vv => AbsUpdateVar (normalize v s) i vv
    | AbsUpdateLoc s i vv => AbsUpdateLoc (normalize v s) i vv
    | AbsUpdateWithLoc s i vv => AbsUpdateWithLoc (normalize v s) i vv
    | x => match findAssignmentsState v (findAssignments v x) x with
           | Some q => q
           | None => x
           end
    end.

Theorem normalizeLeft : forall v left right merge,
    mergeStates (normalize v left) right merge -> mergeStates left right merge.
Proof. admit. Admitted.

Theorem normalizeRight : forall v left right merge,
    mergeStates left (normalize v right) merge -> mergeStates left right merge.
Proof. admit. Admitted.

Theorem normalizeHyp : forall state s b v,
    realizeState state b s -> realizeState (normalize v state) b s.
Proof.
    admit.
Admitted.

