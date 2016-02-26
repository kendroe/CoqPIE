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
Opaque unitEval.

Inductive Context {ev} {eq} {f} {t} {ac} :=
    | StateComponent : @absState ev eq f t ac -> @Context ev eq f t ac
    | AllContext : @absExp ev eq f -> @Context ev eq f t ac -> @Context ev eq f t ac
    | NonZeroExpression : @absExp ev eq f -> @Context ev eq f t ac
    | Domain : nat -> @absExp ev eq f -> @Context ev eq f t ac.

Fixpoint buildExpressionContext {ev} {eq} {f} {t} {ac} (e: @absExp ev eq f) (neg : bool) : list (@Context ev eq f t ac) :=
   if neg then
        match e with
        | AbsFun (AbsOrId) (p::q::nil) => (@buildExpressionContext ev eq f t ac p true)++(@buildExpressionContext ev eq f t ac q true)
        | AbsFun (AbsImplyId) (p::q::nil) => (@buildExpressionContext ev eq f t ac p false)++(@buildExpressionContext ev eq f t ac q true)
        | ~~e => ((NonZeroExpression e)::nil)
        | _ => ((NonZeroExpression (~~e))::nil)
        end
   else
        match e with
        | AbsFun (AbsAndId) (p::q::nil) => (@buildExpressionContext ev eq f t ac p false)++(@buildExpressionContext ev eq f t ac q false)
        | _ => ((NonZeroExpression e)::nil)
        end.

Fixpoint buildNegStateContext {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : list (@Context ev eq f t ac) :=
    match s with
    | AbsOrStar l r => (buildNegStateContext l)++(buildNegStateContext r)
    | AbsLeaf (AbsPredicate) (x::nil) => buildExpressionContext x true
    | _ => nil
    end.

Fixpoint buildStateContext {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : list (@Context ev eq f t ac) :=
    match s with
    | AbsStar l r => (buildStateContext l)++(buildStateContext r)
    | AbsLeaf (AbsPredicate) (x::nil) => buildExpressionContext x false
    | AbsAll e s => map (fun x => (AllContext e x)) (buildStateContext s)
    | _ => (StateComponent s)::nil
    end.

Fixpoint enterAll {ev} {eq} {f} {t} {ac} (e : @absExp ev eq f) (context : list (@Context ev eq f t ac)) :=
    match context with
    | nil => nil
    | ((AllContext ee cc)::r) => if beq_absExp ee e then cc::(enterAll e r) else enterAll e r
    | (f::r) => f::(enterAll e r)
    end.

Fixpoint enterQuant {ev} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac)) :=
    match context with
    | nil => nil
    | ((AllContext ee cc)::r) => enterQuant r
    | (f::r) => f::(enterQuant r)
    end.

Fixpoint findMember {ev} {eq} {f} (base : @absExp ev eq f) (context : list absExp) :=
   match context with
   | (AbsFun (AbsMemberId) (element::tree))::r => if beq_absExp base element then
                                                      Some tree
                                                  else findMember base r
   | (_::r) => findMember base r
   | nil => None
   end.

Fixpoint hasCell {ev} {eq} {f} {t} {ac} (state : @absState ev eq f t ac) (loc : @absExp ev eq f) :=
   match state with
   | AbsLeaf (Id 3) (*AbsCellId*) (l::v::nil) => beq_absExp l loc
   | AbsExistsT s => hasCell s loc
   | AbsAll e s => hasCell s loc
   | AbsExists e s => hasCell s loc
   | AbsEach e s => hasCell s loc
   | AbsStar l r => if (hasCell l loc:bool) then true else hasCell r loc
   | _ => false
   end.

Fixpoint findSmallerVar {ev} {eq} {f} {t} {ac} (v : id) (c : list (@Context ev eq f t ac)) : @absExp ev eq f :=
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

Fixpoint findVar {ev} {eq} {f} {t} {ac} (e : @absExp ev eq f) (c : list (@Context ev eq f t ac)) : @absExp ev eq f :=
    match c with
    | (NonZeroExpression ((AbsVar x)====xx)::r) => if beq_absExp xx e then (AbsVar x) else findVar e r
    | (NonZeroExpression (xx====(AbsVar x))::r) => if beq_absExp xx e then (AbsVar x) else findVar e r
    | (_::r) => findVar e r
    | _ => e
    end.

Fixpoint findVarSubst {ev} {eq} {f} {t} {ac} (vv: id) (c : list (@Context ev eq f t ac)) : @absExp ev eq f :=
    match c with
    | (NonZeroExpression ((AbsVar x)====#c)::r) => if beq_id x vv then #c else (AbsVar vv)
    | (NonZeroExpression (#c====(AbsVar x))::r) => if beq_id x vv then #c else (AbsVar vv)
    | (_::r) => findVarSubst vv r
    | _ => (AbsVar vv)
    end.

Fixpoint noBiggerQuantVars {ev} {eq} {f} (n : nat) (e : @absExp ev eq f) : bool :=
    match e with
    | AbsVar _ => true
    | AbsQVar x => if ble_nat n x then false else true
    | AbsConstVal _ => true
    | AbsFun i l => (fix go l := match l with
                                 | nil => true
                                 | (f::r) => if noBiggerQuantVars n f then go r else false
                                 end) l
    end.

Fixpoint subQVar {ev} {eq} {f} {t} {ac} (v : nat) (c : list (@Context ev eq f t ac)) : @absExp ev eq f :=
    match c with
    | (NonZeroExpression ((AbsQVar x)====y)::r) => if beq_nat v x then (if noBiggerQuantVars x y then y else subQVar v r) else subQVar v r
    | (NonZeroExpression (y====(AbsQVar x))::r) => if beq_nat v x then (if noBiggerQuantVars x y then y else subQVar v r) else subQVar v r
    | (_::r) => subQVar v r
    | _ => AbsQVar v
    end.

Fixpoint pickCt {ev} {eq} {f} {t} {ac} (x : @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
  match context with
  | nil => false
  | ((StateComponent (l |-> f))::r) => if beq_absExp x f then true else pickCt x r
  | ((StateComponent (TREE(root,ff,size,fields)))::r) => if beq_absExp ff x then true else pickCt x r
  | (_::r) => pickCt x r
  end.

Fixpoint pickRt {ev} {eq} {f} {t} {ac} (x : @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
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

Fixpoint allPresent {ev} {eq} {f} {t} {ac} (l : list (@absExp ev eq f)) (e: @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
  match l with
  | nil => true
  | ((AbsVar x)::r) => allPresent r e context
  | (x::r) => if beq_absExp e x then allPresent r e context else if pickCt x context then allPresent r e context else false
  end.

Fixpoint allUsed {ev} {eq} {f} {t} {ac} (l : list (@absExp ev eq f)) (e: @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
  match l with
  | nil => true
  | (x::r) => if beq_absExp e x then allUsed r e context else if pickRt x context then allUsed r e context else false
  end.

Fixpoint findDomain {ev} {eq} {f} {t} {ac} (n : nat) (context : list (@Context ev eq f t ac)) :=
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

Fixpoint hasEquality {ev} {eq} {f} {t} {ac} (c : list (@Context ev eq f t ac)) (e1: @absExp ev eq f) (e2: @absExp ev eq f) :=
    match c with
    | nil => false
    | ((NonZeroExpression (AbsFun (AbsEqualId) (l::r::nil)))::rest) =>
            if (beq_absExp l e1 && beq_absExp r e2) || (beq_absExp l e2 && beq_absExp r e1) then true
            else hasEquality rest e1 e2
    | (_::r) => hasEquality r e1 e2
    end.

Fixpoint hasNonZero {ev} {eq} {f} {t} {ac} (c : list (@Context ev eq f t ac)) (e: @absExp ev eq f) :=
    match c with
    | nil => false
    | ((NonZeroExpression x)::rest) =>
            if beq_absExp e x then true
            else hasNonZero rest e
    | (_::r) => hasNonZero r e
    end.

Fixpoint simplifyExp {ev:Type} {eq: ev -> ev -> bool}
                            {f:id -> list (@Value ev) -> (@Value ev)}
                            {t} {ac}
                            (rule : (list (@Context ev eq f t ac))
                                -> nat -> (@absExp ev eq f) -> (@absExp ev eq f))
                            (context : list (@Context ev eq f t ac))
                            (n :nat)
                            (e : @absExp ev eq f) : @absExp ev eq f :=
    rule context n (match e with
                    | AbsFun (AbsImplyId) (p::q::nil) =>
                             match @simplifyExp ev eq f t ac rule
                                   ((buildExpressionContext q true)++context) n p with
                                   | #0 => #1
                                   | #x => @simplifyExp ev eq f t ac rule context n q
                                   | x => x -->> (@simplifyExp ev eq f t ac rule
                                                  ((buildExpressionContext x false)++context) n q)
                             end
                    | AbsFun (AbsAndId) (p::q::nil) =>
                             match @simplifyExp ev eq f t ac rule
                                   ((buildExpressionContext q false)++context) n p with
                                   | #0 => #0
                                   | #x => @simplifyExp ev eq f t ac rule context n q
                                   | x => x //\\ (@simplifyExp ev eq f t ac rule
                                                  ((buildExpressionContext x false)++context) n q)
                             end
                    | AbsFun (AbsOrId) (p::q::nil) =>
                             match @simplifyExp ev eq f t ac rule
                                   ((buildExpressionContext q true)++context) n p with
                                   | #0 => @simplifyExp ev eq f t ac rule context n q
                                   | #x => #x
                                   | x => x \\// (@simplifyExp ev eq f t ac rule
                                                  ((buildExpressionContext x true)++context) n q)
                             end
                    | AbsFun (AbsIteId) (p::q::r::nil) =>
                             match (@simplifyExp ev eq f t ac rule context n p) with
                             | #x => if beq_nat x 0
                                     then (@simplifyExp ev eq f t ac rule context n r)
                                     else (@simplifyExp ev eq f t ac rule context n q)
                             | x           => (AbsFun (AbsIteId) 
                                                 (x::(@simplifyExp ev eq f t ac rule
                                                       ((buildExpressionContext x false)++context) n q)::
                                                     (@simplifyExp ev eq f t ac rule
                                                       ((buildExpressionContext x true)++context) n r)::nil))
                             end
                    | AbsFun i l => (AbsFun i (map (@simplifyExp ev eq f t ac rule context n) l))
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

Fixpoint findArray {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac))
                   (base : @absExp ev eq f) :=
    match context with
    | nil => None
    | ((StateComponent (ARRAY(_,size,b)))::r) => if beq_absExp b base then
                                                     Some size else findArray r base
    | (_::r) => findArray r base
    end.

Fixpoint findLess {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac))
                  (loc : @absExp ev eq f) (size : @absExp ev eq f) : bool :=
    match context with
    | nil => false
    | (NonZeroExpression (l <<<< s)::r) => if beq_absExp l loc then if beq_absExp s size then true
                                           else findLess r loc size else findLess r loc size
    | (_::r) => findLess r loc size
    end.

Fixpoint validReplace {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac))
                      (base : @absExp ev eq f) (loc : @absExp ev eq f) : bool :=
    match findArray context base with
    | Some size => findLess context loc size
    | None => false
    end.

Fixpoint rangeBotExclude {ev:Type} {eq} {f} (n:nat) (s:@absExp ev eq f) (e:@absExp ev eq f)
                         (v1:@absExp ev eq f) (v2:@absExp ev eq f) :=
     match v1 with
     | AbsQVar m => if beq_nat (S m) n then if beq_absExp (v2++++#1) s then true else false
                    else false
     | _ => false
     end.

Fixpoint rangeExclude {ev:Type} {eq} {f} (n:nat) (s:@absExp ev eq f) (e:@absExp ev eq f)
                      (v1:@absExp ev eq f) (v2:@absExp ev eq f) :=
     match v1 with
     | AbsQVar m => if beq_nat (S m) n then if beq_absExp v2 e then true else rangeBotExclude n s e v1 v2
                    else rangeBotExclude n s e v1 v2
     | _ => rangeBotExclude n s e v1 v2
     end.

Fixpoint notEqual {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac))
                  (e1 : @absExp ev eq f) (e2 : @absExp ev eq f) : bool :=
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

Fixpoint boolExp {ev} {eq} {f} (e : @absExp ev eq f) :=
    match e with
    | ~~x => true
    | a====b => true
    | a<<<<b => true
    | _ => false
    end.

Fixpoint inversionExp {ev} {eq} {f} (a : @absExp ev eq f) (b : @absExp ev eq f)  :=
    match a,b with
    | x,~~y => beq_absExp x y
    | ~~x,y => beq_absExp x y
    | (a\\//b),(c//\\d) => ((inversionExp a c)&&(inversionExp b d)) || ((inversionExp a d)&&(inversionExp b c))
    | (a//\\b),(c\\//d) => ((inversionExp a c)&&(inversionExp b d)) || ((inversionExp a d)&&(inversionExp b c))
    | _,_ => false
    end.

Fixpoint basicExpRule1 {ev:Type} {eq} {f} {t} {ac}
                       (context : list (@Context ev eq f t ac))
                       (n : nat) (e : @absExp ev eq f) : @absExp ev eq f :=
         match e with
         | AbsFun (AbsEqualId) ((#a)::(#b)::nil) => if beq_nat a b then (#1) else (#0)
         | AbsFun (AbsEqualId) ((#0)::(a++++b)::nil) => ((#0====a) //\\ (#0====b))
         | AbsFun (AbsEqualId) ((#a)::(exp++++(#b))::nil) => if ble_nat b a then (#(a-b)====exp) else e
         | AbsFun (AbsEqualId) (e1::e2::nil) => if (beq_absExp e1 e2)
                                                then  @AbsConstVal ev eq f (NatValue 1)
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
                        | NatValue n => nth n l (@AbsConstVal ev eq f NoValue)
                        | _ =>  (@AbsConstVal ev eq f NoValue)
                        end
                     else (AbsFun (AbsNthId) (p::q::nil))
                 | _,a => (AbsFun (AbsNthId) (p::q::nil))
                 end
         | AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil) =>
                 if beq_absExp ff f' then AbsFun (AbsListId) (ff::r)
                 else match f' with
                      | AbsQVar m => match findDomain (m+1) context with
                                     | Some d => if allUsed r d context then
                                                     (AbsFun (AbsFindId) (d::f'::nil))
                                                 else
                                                     (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                                     | None => (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                                     end
                      | _ => (AbsFun (AbsFindId) ((AbsFun (AbsListId) (ff::r))::f'::nil))
                      end
         | AbsFun (AbsFindId) ((AbsFun (AbsFindId) (base::(AbsQVar v1)::nil))::(AbsQVar v2)::nil) =>
                  match findDomain (v2+1) context,findDomain (v1+1) context with
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

Fixpoint simplifyExpression {ev:Type} {eq} {f} {t} {ac} (context : list (@Context ev eq f t ac)) (n : nat)
                            (e : @absExp ev eq f) :=
    @simplifyExp ev eq f t ac basicExpRule1 context n e.
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

Fixpoint eliminatedQuantVar {ev} {eq} {f} {t} {ac} (v : nat) (s : @absState ev eq f t ac) : bool :=
   match s with
   | AbsStar x y => if @eliminatedQuantVar ev eq f t ac v x then @eliminatedQuantVar ev eq f t ac v y
                    else false
   | [v(n)====e] => if beq_nat n v then (if noBiggerQuantVars n e then true else false) else
                       (if hasVnExp e v then false else true)
   | [e====v(n)] => if beq_nat n v then (if noBiggerQuantVars n e then true else false) else
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

Fixpoint reduceFieldRef {ev} {eq} {f} (n : nat ) (e : @absExp ev eq f) : option (absExp * list absExp) :=
    match e with
    | AbsFun (AbsFindId) ((AbsFun (AbsListId) (f::l))::(AbsQVar x)::nil) =>
          if beq_nat x n then
              Some (AbsFun (AbsFindId) ((AbsQVar (S n))::(AbsQVar x)::nil),l)
          else
              None
    | AbsFun i l => match (fix go l := match l with
                                       | (ff::r) => match @reduceFieldRef ev eq f n ff with
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

Fixpoint pickAssignment {ev} {eq} {f} {t} {ac} (n : nat) (s : @absState ev eq f t ac) : option ((@absState ev eq f t ac) * (@absExp ev eq f)) :=
  match s with
  | AbsStar l r => match pickAssignment n l with
                   | Some (s',e) => Some ((AbsStar s' r),e)
                   | None => match pickAssignment n r with
                             | Some (s',e) => Some ((AbsStar l s'),e)
                             | None => None
                             end
                   end
  | AbsExists l s => match pickAssignment n s with
                       | Some (s',e) => Some ((AbsExists l s'),e)
                       | None => None
                       end
  | AbsExistsT s => match pickAssignment n s with
                    | Some (s',e) => Some ((AbsExistsT s'),e)
                    | None => None
                    end
  | [v(x)====e] => if beq_nat x n then if noBiggerQuantVars x e then Some (AbsEmpty,e) else None else None
  | [e====v(x)] => if beq_nat x n then if noBiggerQuantVars x e then Some (AbsEmpty,e) else None else None
  | _ => None
  end.

Fixpoint pickC {ev} {eq} {f} {t} {ac} (x : @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
  match context with
  | nil => false
  | ((StateComponent (l |-> f))::r) => if beq_absExp x f then true else pickC x r
  | (_::r) => pickC x r
  end.

Fixpoint pickPred {ev} {eq} {f} {t} {ac} (x : @absExp ev eq f) (context : list (@Context ev eq f t ac)) : bool :=
  match context with
  | nil => false
  | ((StateComponent ([p]))::r) => if beq_absExp x p then true else pickPred x r
  | ((NonZeroExpression p)::r) => if beq_absExp x p then true else pickPred x r
  | (_::r) => pickPred x r
  end.

Definition unfoldAll {ev} {eq} {f} {t} {ac} (v : @absExp ev eq f) (s : @absState ev eq f t ac) (n : nat) :=
                              match v with
                              | (AbsFun (AbsListId) (ff::l)) =>
                                       fold_left (fun x y => (AbsStar x y))
                                                 (map (fun x => (AbsAll (TreeRecords(x)) s)) l)
                                                 (removeStateVar n (replaceStateVar n ff s))
                              | v' => AbsAll (TreeRecords(v')) s
                              end.

Definition unfoldExists {ev} {eq} {f} {t} {ac} (v : @absExp ev eq f) (s : @absState ev eq f t ac) (n : nat) :=
                              match v with
                              | (AbsFun (AbsListId) (ff::l)) =>
                                       fold_left (fun x y => (AbsOrStar x y))
                                                 (map (fun x => (AbsExists (TreeRecords(x)) s)) l)
                                                 (removeStateVar n (replaceStateVar n ff s))
                              | v' => AbsExists (TreeRecords(v')) s
                              end.

Definition equalsNil {ev} {eq} {f} x := x====(@AbsConstVal ev eq f (ListValue nil)).

Fixpoint simplifySt {ev} {eq} {f} {t} {ac}
                    (erule : (list (@Context ev eq f t ac))
                              -> nat -> (@absExp ev eq f) -> (@absExp ev eq f))
                    (rule : nat -> list (@Context ev eq f t ac) -> (@absState ev eq f t ac) ->
                            (@absState ev eq f t ac))
                    (n : nat)
                    (context : list (@Context ev eq f t ac))
                    (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
    rule n context
       (match s with
        | AbsStar l r => match simplifySt erule rule n ((buildStateContext r)++context) l with
                         | ll => AbsStar ll (simplifySt erule rule n ((buildStateContext ll)++context) r)
                         end
        | AbsOrStar l r => match simplifySt erule rule n ((buildNegStateContext r)++context) l with
                         | ll => AbsOrStar ll (simplifySt erule rule n ((buildNegStateContext ll)++context) r)
                         end
        | AbsExistsT s => AbsExistsT (simplifySt erule rule (S n) (enterQuant context) s)
        | AbsExists l s => AbsExists (simplifyExp erule context n l)
                                     (simplifySt erule rule (S n) ((Domain (S n) l)::(enterQuant context)) s)
        | AbsAll l s => AbsAll (simplifyExp erule context n l)
                               (simplifySt erule rule (S n) ((Domain (S n) l)::(enterAll l context)) s)
        | AbsEach l s => AbsEach (simplifyExp erule context n l)
                                 (simplifySt erule rule (S n) ((Domain (S n) l)::(enterQuant context)) s)
        | AbsLeaf f l => AbsLeaf f (map (simplifyExp erule context n) l)
        | AbsAccumulate i e1 e2 e3 => AbsAccumulate i (simplifyExp erule context n e1)
                                          (simplifyExp erule ((Domain (S n) e1)::(enterQuant context)) (n+1) e2)
                                          (simplifyExp erule context n e3)
        | x => x
        end).

Fixpoint srule {ev} {eq} {f} {t} {ac} (n : nat) (context : list (@Context ev eq f t ac))
                                      (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
     match s return @absState ev eq f t ac with
     | AbsStar l r => match l with
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
     | AbsExistsT s => match pickAssignment n s return @absState ev eq f t ac with
                       | Some (s',e) => removeStateVar n (substState s' n e)
                       | None => if hasVnState s n then AbsExistsT s else removeStateVar n s
                       end
     | AbsExists(TreeRecords(v)) s => if pickC v context then [#0]
                                      else match ((TreeRecords(v)),s) return @absState ev eq f t ac with
                                           | ((TreeRecords(e)),s') => unfoldExists e s' n
                                           | (e,s') => AbsExists e s'
                                           end
     | AbsExists l s =>match pickAssignment n s return @absState ev eq f t ac with
                       | Some (s',e) => removeStateVar n (substState s' n e)
                       | None =>  if hasVnState s n then AbsExists l s else removeStateVar n s
                       end
     | AbsAll(AbsConstVal (ListValue nil)) s => AbsEmpty
     | AbsAll(TreeRecords(v)) s => if pickC v context then AbsEmpty
                                   else match ((TreeRecords(v)),s) return @absState ev eq f t ac with
                                        | (e,(AbsStar l r)) => (AbsStar (AbsAll e l) (AbsAll e r))
                                        | ((TreeRecords(e)),s') => unfoldAll e s' n
                                        | (e,s') => AbsAll e s'
                                        end
     | AbsAll v s => match v,s return @absState ev eq f t ac with
                     | v',AbsStar l r => AbsStar (AbsAll v' l) (AbsAll v' r)
                     | v',s' => AbsAll v' s'
                     end
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
     | (x *\/* [(#0)]) => x
     | ([(#0)] *\/* x) => x
     | [(#n)] => if beq_nat n 0 then [#n] else AbsEmpty
     | AbsLeaf (AbsTreeId) (#0::v::_) => [equalsNil v]
     | x => x
     end.

Fixpoint simplifyState {ev} {eq} {f} {t} {ac} (n : nat) (context : list (@Context ev eq f t ac)) (s : @absState ev eq f t ac) : @absState ev eq f t ac :=
     simplifySt (fun c n e => (basicExpRule1 c n e)) srule n context s.

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

Theorem simplifyEquiv1 {ev} {eq} {f} {t} {ac} : forall (s : @absState ev eq f t ac) s' state,
    s' = @simplifyState ev eq f t ac 0 nil s ->
    realizeState s nil state ->
    realizeState s' nil state.
Proof. admit. Qed.

Definition basicSimplifyEquiv1 := @simplifyEquiv1 unit eq_unit unitEval basicState basicAccumulate.

Theorem simplifyEquivb1 {ev} {eq} {f} {t} {ac} : forall (s : @absState ev eq f t ac) s' b state,
    s' = @simplifyState ev eq f t ac (length b) nil s ->
    realizeState s b state ->
    realizeState s' b state.
Proof. admit. Qed.

Ltac simplifyHyp X:=
    eapply simplifyEquivb1 in X;[compute in X|simplifyState].

Theorem simplifyEquiv2 {ev} {eq} {f} {t} {ac} : forall (s : @absState ev eq f t ac) s' state b,
    s' = @simplifyState ev eq f t ac (length b) nil s ->
    realizeState s' b state -> realizeState s b state.
Proof. admit. Qed.

Theorem simplifyAbsEval {ev} {eq} {f} {t} {ac} : forall (e : @absExp ev eq f) e' b env,
    e' = @simplifyExpression ev eq f t ac nil (length b) e ->
    @absEval ev eq f env b e'= @absEval ev eq f env b e.
Proof. admit. Qed.

Theorem simplifyPre {ev} {eq} {f} {t} {ac} : forall (s : @absState ev eq f t ac) s' cmd post r,
    s' = @simplifyState ev eq f t ac 0 nil s ->
    {{ s' }} cmd {{ post, r }} ->
    {{ s }} cmd {{ post, r }}.
Proof.
    unfold hoare_triple. unfold absExecute. intros.
    eapply H0. eapply simplifyEquiv1. apply H. apply H1.
Qed.

Theorem tsimplifyPre {ev} {eq} {f} {t} {ac} : forall (s : @absState ev eq f t ac) s' cmd post r,
    {{ s' }} cmd {{ post, r }} ->
    s' = @simplifyState ev eq f t ac 0 nil s ->
    {{ s }} cmd {{ post, r }}.
Proof.
    unfold hoare_triple. unfold absExecute. intros.
    eapply H. eapply simplifyEquiv1. apply H0. apply H1.
Qed.

Opaque basicEval.

Ltac simp := eapply simplifyPre;[(compute;reflexivity)|idtac].
Ltac simplifyPre := repeat (progress simp).

Ltac simpBasic := eapply (@simplifyPre unit eq_unit
                    (@basicEval unit)
                    (@basicState unit) (@basicAccumulate unit eq_unit) tt)
                    ;[simplifyState|(instantiate;simpl)] || idtac.
Ltac simplifyPreBasic := repeat (progress simpBasic).

Theorem mergeSimplifyLeft {ev} {eq} {f} {t} {ac} : forall (P1 : @absState ev eq f t ac) P1' P2 P,
    P1' = @simplifyState ev eq f t ac 0 nil P1 ->
    mergeStates P1' P2 P ->
    mergeStates P1 P2 P.
Proof. unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. eapply H1. eapply simplifyEquiv1. reflexivity. apply H. intros. apply H2. apply H.
Qed.

Theorem mergeSimplifyRight {ev} {eq} {f} {t} {ac} : forall (P1 : @absState ev eq f t ac) P2 P2' P,
    P2' = @simplifyState ev eq f t ac 0 nil P2 ->
    mergeStates P1 P2' P ->
    mergeStates P1 P2 P.
Proof. unfold mergeStates. intros. inversion H0. subst. clear H0. split.
    intros. apply H1. apply H. intros. eapply H2. eapply simplifyEquiv1.
    reflexivity. eapply H.
Qed.

Ltac simpleft := eapply mergeSimplifyLeft;[(simpl;reflexivity)|idtac].
Ltac mergeSimplifyLeft := repeat (progress simpleft).

Ltac simpright := eapply mergeSimplifyRight;[(simpl;reflexivity)|idtac].
Ltac mergeSimplifyRight := repeat (progress simpright).
