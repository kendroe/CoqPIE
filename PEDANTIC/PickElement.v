(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * PickElement.v
 * This file contains definitions and tactics for picking elements out of an
 * abstract state.
 *
 * Some key definitions:
 *     spickElement - pick an element in an absState
 *     pickElement - a variant of spickElement
 *     pickElementNi - a variant of pickElement
 *     pick2Rs - pick two matching R terms from two separate absStates
 *     pick2RsNi - variant of pick2Rs
 *     allPredicates - determine whether a state has been reduced entirely to predicates
 *
 **********************************************************************************)

Require Export SfLib.
Require Export ImpHeap.
Require Export AbsState.
Require Export AbsStateInstance.
Require Export Coq.Logic.FunctionalExtensionality.
Opaque unitEval.

Fixpoint delete_nat (n : nat) (l : list nat) :=
    match l with
    | a::b => if beq_nat n a then delete_nat n b else a::(delete_nat n b)
    | nil => nil
    end.

Fixpoint beq_nat_list (l1 : list nat) (l2 : list nat) : bool :=
    match (l1,l2) with
    | (f1::r1,f2::r2) => if beq_nat f1 f2 then beq_nat_list r1 r2 else false
    | (nil,nil) => true
    | _ => false
    end.

Fixpoint mem_pair (x : nat * nat) (l : list (nat * nat)) : bool :=
    match (x,l) with
    | ((x1,x2),((f1,f2)::r)) => if beq_nat x1 f1 then if beq_nat x2 f2 then true else mem_pair x r else mem_pair x r
    | _ => false
    end.

Fixpoint no_first (x : nat) (l : list (nat * nat)) : bool :=
    match l with
    | ((f1,f2)::r) => if beq_nat x f1 then false else no_first x r
    | _ => true
    end.

Fixpoint no_second (x : nat) (l : list (nat * nat)) : bool :=
    match l with
    | ((f1,f2)::r) => if beq_nat x f2 then false else no_second x r
    | _ => true
    end.

Fixpoint noQVarExp {ev} {eq} {f} (e : @absExp ev eq f) : bool :=
   match e with
   | AbsConstVal v => true
   | AbsVar v => true
   | AbsQVar vv => false
   | AbsFun i l => (fix go (l : list (@absExp ev eq f)) := match l with | nil => true | (f::r) => if noQVarExp f then go r else false end) l
   end.

Fixpoint noQVarState {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : bool :=
   match s with
    | AbsStar s1 s2 => if noQVarState s1 then noQVarState s2 else false
    | AbsOrStar s1 s2 => if noQVarState s1 then noQVarState s2 else false
    | AbsExistsT s => noQVarState s
    | AbsExists e s => if noQVarExp e then noQVarState s else false
    | AbsAll e s => if noQVarExp e then noQVarState s else false
    | AbsEach e s => if noQVarExp e then noQVarState s else false
    | AbsEmpty => true
    | AbsLeaf i l =>  (fix go (l : list (@absExp ev eq f)) := match l with | nil => true | (f::r) => if noQVarExp f then go r else false end) l
    | AbsAccumulate id e1 e2 e3 =>
          if noQVarExp e1 then
          if noQVarExp e2 then
          noQVarExp e3 else false else false
   | AbsMagicWand s1 s2 => if noQVarState s1 then noQVarState s2 else false
   | AbsUpdateVar s i e => if noQVarExp e then noQVarState s else false
   | AbsUpdState s1 s2 s3 => if noQVarState s1 then if noQVarState s2 then noQVarState s3 else false else false
   end.

Fixpoint mem_absExp {ev} {eq} {f} (e : absExp) (l : list (@absExp ev eq f)) :=
    match l with
    | (f::r) => if beq_absExp e f then true else mem_absExp e r
    | _ => false
    end.

Fixpoint common_element {ev} {eq} {f} (l1 : list (@absExp ev eq f)) (l2 : list (@absExp ev eq f)) : option (@absExp ev eq f) :=
    match l1 with
    | (f::r) => if (mem_absExp f l2) then Some f else common_element r l2
    | _ => None
    end.

Fixpoint equiv_absExp2 {ev} {eq} {f} (e1 : (@absExp ev eq f)) (e2 : (@absExp ev eq f)) (s1 : list (@absExp ev eq f)) (equiv2 : list (list (@absExp ev eq f))) : option (@absExp ev eq f) :=
    match equiv2 with
    | (f::r) => if mem_absExp e2 f then common_element s1 f else equiv_absExp2 e1 e2 s1 r
    | _ => if mem_absExp e2 s1 then Some e2 else None
    end.

Fixpoint equiv_absExp {ev} {eq} {f} (e1 : (@absExp ev eq f)) (e2 : (@absExp ev eq f)) (equiv1 : list (list (@absExp ev eq f))) (equiv2 : list (list (@absExp ev eq f))) : option (@absExp ev eq f) :=
    match equiv1 with
    | (f::r) => if mem_absExp e1 f then equiv_absExp2 e1 e2 f equiv2 else equiv_absExp e1 e2 r equiv2
    | _ => equiv_absExp2 e1 e2 (e1::nil) equiv2
    end.

Definition pair_apply {t} {r} (f : t -> t -> r -> option (r*t*t)) : r -> list t -> list t -> option (r * list t * list t) :=
    fix go r l1 l2 :=
    match l1,l2 with
    | nil,nil => Some (r,nil,nil)
    | f1::r1,f2::r2 => match f f1 f2 r with
                         | Some (rr,t1,t2) => match go rr r1 r2 with
                                              | Some (rrr,tl1,tl2) => Some (rrr,t1::tl1,t2::tl2)
                                              | None => None
                                              end
                         | None => None
                         end
    | _, _ => None
    end.

Fixpoint ml (n : nat) (pairs : list (nat * nat)) : option nat :=
    match pairs with
    | nil => None
    | ((a,b)::r) => if beq_nat b n then Some a else ml n r
    end.

Fixpoint strip_pair (n1 : nat) (n2 : nat) (pairs : list (nat * nat)) : list (nat * nat) :=
    match pairs with
    | nil => nil
    | ((a,b)::r) => if beq_nat n1 a then if beq_nat n2 b then strip_pair n1 n2 r
                    else ((a,b)::(strip_pair n1 n2 r)) else ((a,b)::(strip_pair n1 n2 r))
    end.

Fixpoint mapExpLeft {ev} {eq} {f} (t1 : nat) (t2 : nat) (pairs : list (nat * nat)) (e : @absExp ev eq f) : option (@absExp ev eq f) :=
   match e with
   | AbsConstVal v => Some (AbsConstVal v)
   | AbsVar v => Some (AbsVar v)
   | AbsQVar vv => if ble_nat t2 vv then
                       Some (AbsQVar (vv+t1-t2))
                   else
                       match ml vv pairs with
                       | Some x => Some (AbsQVar x)
                       | None => None
                       end
   | AbsFun i l => match (fix go (l : list (@absExp ev eq f)) :=
                              match l with
                              | nil => Some nil
                              | (f::r) => match (mapExpLeft t1 t2 pairs f,go r) with
                                          | (Some ff,Some rr) => Some (ff::rr)
                                          | _ => None
                                          end
                          end) l with
                   | Some l => Some (AbsFun i l)
                   | None => None
                   end
   end.

Fixpoint mapStateLeft {ev} {eq} {f} {t} {ac} (t1 : nat) (t2 : nat) (pairs : list (nat * nat)) (s : @absState ev eq f t ac) : option (@absState ev eq f t ac) :=
   match s with
    | AbsStar s1 s2 => match mapStateLeft t1 t2 pairs s1,mapStateLeft t1 t2 pairs s2 with
                       | Some s1,Some s2 => Some (AbsStar s1 s2)
                       | _,_ => None
                       end
    | AbsOrStar s1 s2 => match mapStateLeft t1 t2 pairs s1,mapStateLeft t1 t2 pairs s2 with
                         | Some s1,Some s2 => Some (AbsOrStar s1 s2)
                         | _,_ => None
                         end
    | AbsExistsT s => match mapStateLeft t1 t2 pairs s with
                      | Some s' => Some (AbsExistsT s')
                      | _ => None
                      end
    | AbsExists e s => match mapStateLeft t1 t2 pairs s,mapExpLeft t1 t2 pairs e with
                       | Some s,Some e => Some (AbsExists e s)
                       | _,_ => None
                       end
    | AbsAll e s => match mapStateLeft t1 t2 pairs s,mapExpLeft t1 t2 pairs e with
                    | Some s,Some e => Some (AbsAll e s)
                    | _,_ => None
                    end
    | AbsEach e s => match mapStateLeft t1 t2 pairs s,mapExpLeft t1 t2 pairs e with
                     | Some s,Some e => Some (AbsEach e s)
                     | _,_ => None
                     end
    | AbsEmpty => Some AbsEmpty
    | AbsLeaf i l => match (fix go (l : list (@absExp ev eq f)) :=
                              match l with
                              | nil => Some nil
                              | (f::r) => match (mapExpLeft t1 t2 pairs f,go r) with
                                          | (Some ff,Some rr) => Some (ff::rr)
                                          | _ => None
                                          end
                          end) l with
                   | Some l => Some (AbsLeaf i l)
                   | None => None
                   end
   | _ => None
   end.

   (*| AbsAccumulate id1 l1 id2 e l2 ee =>
          if noQVarExp e then
          if noQVarExp ee then
          if (fix go (l : list (@absExp ev eq f)) := match l with | nil => true | (f::r) => if noQVarExp f then go r else false end) l1 then
             (fix go (l : list (@absExp ev eq f)) := match l with | nil => true | (f::r) => if noQVarExp f then go r else false end) l2
          else false else false else false*)

(*
 * match two expressions
 *
 * Determine whether two expressions are identical with the exception of bound variable references.
 * If they are, then return the mapping between bound variable references in one to references in the
 * other
 *
 * Parameters:
 *     equivl - list of subexpressions in left (first exp) known to be equivalent
 *     equivr - list of subexpressions in right (second exp) known to be equivalent
 *        Subterms in this set are all treated as equal by the algorithm
 *     limit1 - bound variable upper limit for first expression
 *     limit2 - bound variable upper limit for second expression
 *        Bound variables in e1 and e2 may exceed limit1 and limit2 resp.  However, then
 *        v1-limit1=v2-limit for the subterms to be equivalent.  No pairing is done in this
 *        case.
 *     e1 - first expression
 *     e2 - second expression
 *     pairs - bound variables already paired up
 * Returned:
 *     list of bound variable pairings.
 *)
Definition funFix {ev} {eq} {f} (x : option ((list (nat * nat)) * (list (@absExp ev eq f)) * (list (@absExp ev eq f)))) i :=
    match x with
    | Some (p,tl1,tl2) => Some (p,@AbsFun ev eq f i tl1,@AbsFun ev eq f i tl2)
    | None => None
    end.

Fixpoint match_expression {ev} {eq} {f} (equivl : list (list (@absExp ev eq f))) (equivr : list (list (@absExp ev eq f))) (limit1 : nat) (limit2 : nat) (e1 : @absExp ev eq f) (e2 : @absExp ev eq f) (pairs : list (nat * nat)) : option ((list (nat * nat)) * (@absExp ev eq f) * (@absExp ev eq f)) :=
    match (e1,e2) with
    | (AbsConstVal v1,AbsConstVal v2) => if @beq_val ev eq v1 v2 then Some (pairs,AbsConstVal v1,AbsConstVal v2) else None
    | (AbsVar v1,AbsVar v2) => if beq_id v1 v2 then (Some (pairs,AbsVar v1, AbsVar v2)) else
                                   match equiv_absExp (AbsVar v1) (AbsVar v2) equivl equivr with
                                   | Some t => Some (pairs,t,t)
                                   | None => None
                                   end
    | (AbsQVar v1,AbsQVar v2) => if ble_nat limit1 v1 then
                                     if beq_nat v1 ((v2+limit1)-limit2) then Some (pairs,AbsQVar v1,AbsQVar v2) else None
                                 else if mem_pair (v1,v2) pairs then
                                     Some (pairs,AbsQVar v1,AbsQVar v2)
                                 else if ble_nat limit2 v2 then
                                     None
                                 else if no_first v1 pairs then
                                     if no_second v2 pairs then
                                         Some ((v1,v2)::pairs,AbsQVar v1,AbsQVar v2)
                                     else None
                                 else None
    | (AbsFun i1 el1,AbsFun i2 el2) => if beq_id i1 i2 then
                                           funFix (pair_apply (match_expression equivl equivr limit1 limit2) pairs el1 el2) i1
                                       else None
    | (l,r) => match equiv_absExp l r equivl equivr with
               | Some t => if noQVarExp t then Some (pairs,t,t) else None
               | None => None
               end
    end.

(*
 * Match two states if they are identical except for bound variable references as above for
 * expressions
 *
 * Parameters:
 *     limit1 - bound variable upper limit for first expression
 *     limit2 - bound variable upper limit for second expression
 *        Bound variables in e1 and e2 may exceed limit1 and limit2 resp.  However, then
 *        v1-limit1=v2-limit for the subterms to be equivalent.  No pairing is done in this
 *        case.
 *     pairs - bound variables already paired up
 *     equivl - list of subexpressions in left (first exp) known to be equivalent
 *     equivr - list of subexpressions in right (second exp) known to be equivalent
 *        Subterms in this set are all treated as equal by the algorithm
 *     l - first state
 *     r - second state
 * Returned:
 *     list of bound variable pairings.
 *)
Definition build_leaf {ev} {eq} {f} {t} {ac} (x : option ((list (nat * nat)) * (list (@absExp ev eq f)) * (list (@absExp ev eq f)))) i :=
    match x with
    | Some (p,l1,l2) => Some (p,@AbsLeaf ev eq f t ac i l1,@AbsLeaf ev eq f t ac i l2)
    | None => None
    end.

(*Definition build_acc {ev} {eq} {f} {t} {ac} i
                     (el : option ((list (nat * nat)) * (list (@absExp ev eq f)) * (list (@absExp ev eq f))))
                     ii
                     (el : option ((list (nat * nat)) * (list (@absExp ev eq f)) * (list (@absExp ev eq f))))*)

Fixpoint match_state {ev} {eq} {f} {t} {ac} (limit1 : nat) (limit2 : nat) (pairs : list (nat * nat)) (equivl : list (list (@absExp ev eq f))) (equivr : list (list (@absExp ev eq f))) (l : @absState ev eq f t ac) (r : @absState ev eq f t ac) : option ((list (nat * nat)) * (@absState ev eq f t ac) * (@absState ev eq f t ac)) :=
   match (l,r) with
    | (AbsStar l1 l2,AbsStar r1 r2) => match match_state limit1 limit2 pairs equivl equivr l1 r1 with
                                             | Some (p,tl1,tr1) => match match_state limit1 limit2 p equivl equivr l2 r2 with
                                                                   | Some (p,tl2,tr2) => Some (p,AbsStar tl1 tl2,AbsStar tr1 tr2)
                                                                   | None => None
                                                                   end
                                             | None => None
                                       end
    | (AbsOrStar l1 l2,AbsOrStar r1 r2) => match match_state limit1 limit2 pairs equivl equivr l1 r1 with
                                                 | Some (p,tl1,tr1) => match match_state limit1 limit2 p equivl equivr l2 r2 with
                                                                       | Some (p,tl2,tr2) => Some (p,AbsOrStar tl1 tl2,AbsOrStar tr1 tr2)
                                                                       | None => None
                                                                       end
                                                 | None => None
                                           end
    | (AbsEmpty,AbsEmpty) => Some (pairs,AbsEmpty,AbsEmpty)
    | (AbsExists e1 s1,AbsExists e2 s2) => match match_expression equivl equivr limit1 limit2 e1 e2 pairs with
                                           | Some (r,re1,re2) => match match_state (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                                 | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsExists re1 rs1,AbsExists re2 rs2)
                                                                 | None => None
                                                                 end
                                           | None => None
                                           end
    | (AbsAll e1 s1,AbsAll e2 s2) => match match_expression equivl equivr limit1 limit2 e1 e2 pairs with
                                     | Some (r,re1,re2) => match match_state (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                           | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsAll re1 rs1,AbsAll re2 rs2)
                                                           | None => None
                                                           end
                                     | None => None
                                     end
    | (AbsEach e1 s1,AbsEach e2 s2) => match match_expression equivl equivr limit1 limit2 e1 e2 pairs with
                                       | Some (r,re1,re2) => match match_state (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                             | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsEach re1 rs1,AbsEach re2 rs2)
                                                             | None => None
                                                             end
                                       | None => None
                                       end
    | (AbsExistsT s1,AbsExistsT s2) => match match_state (limit1+1) (limit2+1) ((limit1,limit2)::pairs) equivl equivr s1 s2 with
                                       | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsExistsT rs1,AbsExistsT rs2)
                                       | None => None
                                       end
    | (AbsLeaf i1 el1,AbsLeaf i2 el2) => if beq_id i1 i2 then 
                                       build_leaf (pair_apply (match_expression equivl equivr limit1 limit2) pairs el1 el2) i1
                                   else None
    | (AbsAccumulate i1 e1a e1b e1c,AbsAccumulate i2 e2a e2b e2c) =>
          if beq_id i1 i2 then
              match match_expression equivl equivr limit1 limit2 e1a e2a pairs with
              | Some (p,re1a,re2a) => match match_expression equivl equivr limit1 limit2 e1b e2b p with
                                      | Some (p,re1b,re2b) => match match_expression equivl equivr limit1 limit2 e1c e2c p with
                                                              | Some (p,re1c,re2c) => Some (p,AbsAccumulate i1 re1a re1b re1c,AbsAccumulate i2 re2a re2b re2c)
                                                              | None => None
                                                              end
                                      | None => None
                                      end
              | None => None
              end
          else None
    | _ => None
    end.

(*
 * match two expressions
 *
 * Determine whether two expressions are identical with the exception of bound variable references.
 * If they are, then return the mapping between bound variable references in one to references in the
 * other.  This is the same as match_expression except that no new bound variable paris are added
 * to 'pairs'
 *
 * Parameters:
 *     equivl - list of subexpressions in left (first exp) known to be equivalent
 *     equivr - list of subexpressions in right (second exp) known to be equivalent
 *        Subterms in this set are all treated as equal by the algorithm
 *     limit1 - bound variable upper limit for first expression
 *     limit2 - bound variable upper limit for second expression
 *        Bound variables in e1 and e2 may exceed limit1 and limit2 resp.  However, then
 *        v1-limit1=v2-limit for the subterms to be equivalent.  No pairing is done in this
 *        case.
 *     e1 - first expression
 *     e2 - second expression
 *     pairs - bound variables already paired up
 * Returned:
 *     list of bound variable pairings.
 *)
Fixpoint match_expression_ni {ev} {eq} {f} (equivl : list (list (@absExp ev eq f))) (equivr : list (list (@absExp ev eq f))) (limit1 : nat) (limit2 : nat) (e1 : @absExp ev  eq f) (e2 : @absExp ev eq f) (pairs : list (nat * nat)) : option ((list (nat * nat)) * (@absExp ev eq f) * (@absExp ev eq f)) :=
    match (e1,e2) with
    | (AbsConstVal v1,AbsConstVal v2) => if @beq_val ev eq v1 v2 then Some (pairs,AbsConstVal v1,AbsConstVal v2) else None
    | (AbsVar v1,AbsVar v2) => if beq_id v1 v2 then (Some (pairs,AbsVar v1, AbsVar v2)) else
                                   match equiv_absExp (AbsVar v1) (AbsVar v2) equivl equivr with
                                   | Some t => Some (pairs,t,t)
                                   | None => None
                                   end
    | (AbsQVar v1,AbsQVar v2) => if ble_nat limit1 v1 then
                                     if beq_nat v1 ((v2+limit1)-limit2) then Some (pairs,AbsQVar v1,AbsQVar v2) else None
                                 else if mem_pair (v1,v2) pairs then
                                     Some (pairs,AbsQVar v1,AbsQVar v2)
                                 else if ble_nat limit2 v2 then
                                     None
                                 else None
    | (AbsFun i1 el1,AbsFun i2 el2) => if beq_id i1 i2 then
                                           funFix (pair_apply (match_expression_ni equivl equivr limit1 limit2) pairs el1 el2) i1
                                       else None
    | (l,r) => match equiv_absExp l r equivl equivr with
               | Some t => if noQVarExp t then Some (pairs,t,t) else None
               | None => None
               end
    end.

(*
 * Match two states if they are identical except for bound variable references (but without adding new
 * pairs) as above for expressions
 *
 * Parameters:
 *     limit1 - bound variable upper limit for first expression
 *     limit2 - bound variable upper limit for second expression
 *        Bound variables in e1 and e2 may exceed limit1 and limit2 resp.  However, then
 *        v1-limit1=v2-limit for the subterms to be equivalent.  No pairing is done in this
 *        case.
 *     pairs - bound variables already paired up
 *     equivl - list of subexpressions in left (first exp) known to be equivalent
 *     equivr - list of subexpressions in right (second exp) known to be equivalent
 *        Subterms in this set are all treated as equal by the algorithm
 *     l - first state
 *     r - second state
 * Returned:
 *     list of bound variable pairings.
 *)
Fixpoint match_state_ni {ev} {eq} {f} {t} {ac} (limit1 : nat) (limit2 : nat) (pairs : list (nat * nat)) (equivl : list (list (@absExp ev eq f))) (equivr : list (list (@absExp ev eq f))) (l : @absState ev eq f t ac) (r : @absState ev eq f t ac) : option ((list (nat * nat)) * (@absState ev eq f t ac) * (@absState ev eq f t ac)) :=
    match (l,r) with
    | (AbsStar l1 l2,AbsStar r1 r2) => match match_state_ni limit1 limit2 pairs equivl equivr l1 r1 with
                                             | Some (p,tl1,tr1) => match match_state_ni limit1 limit2 p equivl equivr l2 r2 with
                                                                   | Some (p,tl2,tr2) => Some (p,AbsStar tl1 tl2,AbsStar tr1 tr2)
                                                                   | None => None
                                                                   end
                                             | None => None
                                       end
    | (AbsOrStar l1 l2,AbsOrStar r1 r2) => match match_state_ni limit1 limit2 pairs equivl equivr l1 r1 with
                                                 | Some (p,tl1,tr1) => match match_state_ni limit1 limit2 p equivl equivr l2 r2 with
                                                                       | Some (p,tl2,tr2) => Some (p,AbsOrStar tl1 tl2,AbsOrStar tr1 tr2)
                                                                       | None => None
                                                                       end
                                                 | None => None
                                           end
    | (AbsEmpty,AbsEmpty) => Some (pairs,AbsEmpty,AbsEmpty)
    | (AbsExists e1 s1,AbsExists e2 s2) => match match_expression_ni equivl equivr limit1 limit2 e1 e2 pairs with
                                           | Some (r,re1,re2) => match match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                                 | Some (p, rs1, rs2) => Some (strip_pair limit1 limit2 p,AbsExists re1 rs1,AbsExists re2 rs2)
                                                                 | None => None
                                                                 end
                                           | None => None
                                           end
    | (AbsAll e1 s1,AbsAll e2 s2) => match match_expression_ni equivl equivr limit1 limit2 e1 e2 pairs with
                                     | Some (r,re1,re2) => match match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                           | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsAll re1 rs1,AbsAll re2 rs2)
                                                           | None => None
                                                           end
                                     | None => None
                                     end
    | (AbsEach e1 s1,AbsEach e2 s2) => match match_expression_ni equivl equivr limit1 limit2 e1 e2 pairs with
                                       | Some (r,re1,re2) => match match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::r) equivl equivr s1 s2 with
                                                             | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p,AbsEach re1 rs1,AbsEach re2 rs2)
                                                             | None => None
                                                             end
                                       | None => None
                                       end
    | (AbsExistsT s1,AbsExistsT s2) => match match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::pairs) equivl equivr s1 s2 with
                                       | Some (p,rs1,rs2) => Some (strip_pair limit1 limit2 p, AbsExistsT rs1, AbsExistsT rs2)
                                       | None => None
                                       end
    | (AbsLeaf i1 el1,AbsLeaf i2 el2) => if beq_id i1 i2 then 
                                       build_leaf (pair_apply (match_expression_ni equivl equivr limit1 limit2) pairs el1 el2) i1
                                   else None
    | (AbsAccumulate i1 e1a e1b e1c,AbsAccumulate i2 e2a e2b e2c) =>
          if beq_id i1 i2 then
              match match_expression_ni equivl equivr limit1 limit2 e1a e2a pairs with
              | Some (p,re1a,re2a) => match match_expression_ni equivl equivr limit1 limit2 e1b e2b p with
                                      | Some (p,re1b,re2b) => match match_expression_ni equivl equivr limit1 limit2 e1c e2c p with
                                                              | Some (p,re1c,re2c) => Some (p,AbsAccumulate i1 re1a re1b re1c,AbsAccumulate i2 re2a re2b re2c)
                                                              | None => None
                                                              end
                                      | None => None
                                      end
              | None => None
              end
          else None
    | _ => None
    end.

(*
 * Pick a component out of a state
 *
 * Parameters:
 *   #1 : absState - input of the state to find the element in
 *   #2 : absState - output of the component
 *   #3 : absState - output of the original state where that component is
 *                   replaced with EmptyFun
 *)
Inductive spickElement {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> @absState ev eq f t ac -> @absState ev eq f t ac -> Prop :=
  | PESComposeLeft : forall l r e l',
                    spickElement l e l' ->
                    spickElement (AbsStar l r) e (AbsStar l' r)
  | PESComposeRight : forall l r e r',
                     spickElement r e r' ->
                     spickElement (AbsStar l r) e (AbsStar l r')
  | PESAll : forall e p,
             spickElement (AbsAll e p) (AbsAll e p) AbsEmpty
  | PESEach : forall e p,
             spickElement (AbsEach e p) (AbsEach e p) AbsEmpty
  | PESR : forall i el,
          spickElement (AbsLeaf i el) (AbsLeaf i el) AbsEmpty
  | PESOR : forall l r,
          spickElement (l *\/* r) (l *\/* r) AbsEmpty.

Ltac solveSPickElement :=
     solve [(eapply PESComposeLeft;solveSPickElement) |
            (eapply PESComposeRight;solveSPickElement) |
            (eapply PESR) |
            (eapply PESAll) |
            (eapply PESEach) |
            (eapply PESOR)].

(*
 * Pick a component out of a state
 *
 * Parameters:
 *   #1 : absState - input of the state to find the element in
 *   #2 : list (nat * nat) - bound variable mappings (used in match_state)
 *   #3 : nat - limit1 used in match_state
 *   #4 : nat - limit2 used in match_state
 *   #5 : list (list absExp) - equiv1 used in match_state
 *   #6 : list (list absExp) - equiv2 used in match_state
 *   #7 : absState - element to pick out
 *   #8 : absState - element picked out (with bound variables mapped over)
 *   #9 : absState - remainder of term (with picked out element removed)
 *   #10 : list (list nat) - returned pairs (with additional pairs from match_state)
 *)
Inductive pickElement {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> (list (nat * nat)) -> nat -> nat -> (list (list (@absExp ev eq f))) -> (list (list (@absExp ev eq f))) -> @absState ev eq f t ac -> @absState ev eq f t ac -> @absState ev eq f t ac -> (list (nat * nat)) -> Prop :=
  | PEComposeLeft : forall l r e e' l' vars vars' limit1 limit2 eq1 eq2,
                    pickElement l vars limit1 limit2 eq1 eq2 e e' l' vars' ->
                    pickElement (AbsStar l r) vars limit1 limit2 eq1 eq2 e e' (AbsStar l' r) vars'
  | PEComposeRight : forall l r e e' r' vars vars' limit1 limit2 eq1 eq2,
                     pickElement r vars limit1 limit2 eq1 eq2 e e' r' vars' ->
                     pickElement (AbsStar l r) vars limit1 limit2 eq1 eq2 e e' (AbsStar l r') vars'
  (*| PEAll : forall i l s,
            pickElement (AbsAll i l s) (AbsAll t s) AbsEmpty*)
  | PER : forall i l l' vars vars' limit1 limit2 eq1 eq2 tl tl',
          Some (vars',tl,tl') = pair_apply (match_expression limit1 limit2 eq1 eq2) vars l l' ->
          pickElement (AbsLeaf i l') vars eq1 eq2 limit1 limit2 (AbsLeaf i l) (AbsLeaf i tl') AbsEmpty vars'.

Ltac solvePickElement :=
     solve [(eapply PEComposeLeft;solvePickElement) |
            (eapply PEComposeRight;solvePickElement) |
            (eapply PER;simpl;reflexivity)].


(*
 * Pick a component out of a state (Same as above except that the first
 * argument in an AbsLeaf match uses pick_element_ni so as not to add pairs
 *
 * Parameters:
 *   #1 : absState - input of the state to find the element in
 *   #2 : list (nat * nat) - bound variable mappings (used in match_state)
 *   #3 : nat - limit1 used in match_state
 *   #4 : nat - limit2 used in match_state
 *   #5 : list (list absExp) - equiv1 used in match_state
 *   #6 : list (list absExp) - equiv2 used in match_state
 *   #7 : absState - element to pick out
 *   #8 : absState - element picked out (with bound variables mapped over)
 *   #9 : absState - remainder of term (with picked out element removed)
 *   #10 : list (list nat) - returned pairs (with additional pairs from match_state)
 *)
Inductive pickElementNi {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> (list (nat * nat)) -> nat -> nat -> (list (list (@absExp ev eq f))) -> (list (list (@absExp ev eq f))) -> @absState ev eq f t ac -> @absState ev eq f t ac -> @absState ev eq f t ac -> (list (nat * nat)) -> Prop :=
  | PEComposeLeftNi : forall l r e e' l' vars vars' limit1 limit2 eq1 eq2,
                      pickElementNi l vars limit1 limit2 eq1 eq2 e e' l' vars' ->
                      pickElementNi (AbsStar l r) vars limit1 limit2 eq1 eq2 e e' (AbsStar l' r) vars'
  | PEComposeRightNi : forall l r e e' r' vars vars' limit1 limit2 eq1 eq2,
                       pickElementNi r vars limit1 limit2 eq1 eq2 e e' r' vars' ->
                       pickElementNi (AbsStar l r) vars limit1 limit2 eq1 eq2 e e' (AbsStar l r') vars'
  (*| PEPredicateNi : forall P P' vars vars' limit1 limit2 eq1 eq2,
                    Some vars' = match_expression P P' limit1 limit2 vars eq1 eq2 ->
                    pickElementNi (AbsPredicate P') vars limit1 limit2 eq1 eq2 (AbsPredicate P) (AbsPredicate P') AbsEmpty vars'
  | PEExists : forall t s vars vars' vars'' limit1 limit2,
               pickElement (AbsExists t s) (AbsExists t s) AbsEmpty*)
  | PEAllNi : forall tt s tt' s' vars eq1 eq2 limit1 limit2 vars' vars'' vars''' ttl ttl' sl sl',
              Some (vars',ttl,ttl') = match_expression_ni eq1 eq2 limit1 limit2 tt tt' vars ->
              Some (vars'',sl,sl') = match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::vars) eq1 eq2 s s' ->
              vars''' = strip_pair limit1 limit2 vars'' ->
              pickElementNi (AbsAll tt' s') vars limit1 limit2 eq1 eq2 (AbsAll tt s) (AbsAll ttl' sl') AbsEmpty vars'''
  | PEExistsNi : forall tt s tt' s' vars eq1 eq2 limit1 limit2 vars' vars'' vars''' ttl ttl' sl sl',
              Some (vars',ttl,ttl') = match_expression_ni eq1 eq2 limit1 limit2 tt tt' vars ->
              Some (vars'',sl,sl') = match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::vars) eq1 eq2 s s' ->
              vars''' = strip_pair limit1 limit2 vars'' ->
              pickElementNi (AbsExists tt' s') vars limit1 limit2 eq1 eq2 (AbsExists tt s) (AbsExists ttl' sl') AbsEmpty vars'''
  | PEEachNi : forall tt s tt' s' vars eq1 eq2 limit1 limit2 vars' vars'' vars''' ttl ttl' sl sl',
              Some (vars',ttl,ttl') = match_expression_ni eq1 eq2 limit1 limit2 tt tt' vars ->
              Some (vars'',sl,sl') = match_state_ni (limit1+1) (limit2+1) ((limit1,limit2)::vars) eq1 eq2 s s' ->
              vars''' = strip_pair limit1 limit2 vars'' ->
              pickElementNi (AbsEach tt' s') vars limit1 limit2 eq1 eq2 (AbsEach tt s) (AbsEach ttl' sl') AbsEmpty vars'''
  | PERNi : forall r r' i h h' vars vars' vars'' limit1 limit2 eq1 eq2 rl rl' hl hl' eqq1 eqq2,
          match (@AbsLeaf ev eq f t ac i (r::h)) with
          | [a====b] => (nil,nil)
          | _ => (limit1,limit2)
          end = (eqq1,eqq2) ->   
          Some (vars',rl,rl') = match_expression_ni eqq1 eqq2 eq1 eq2 r r' vars ->
          Some (vars'',hl,hl') = pair_apply (match_expression limit1 limit2 eq1 eq2) vars' h h' ->
          pickElementNi (AbsLeaf i (r'::h')) vars eq1 eq2 limit1 limit2 (AbsLeaf i (r::h)) (AbsLeaf i (rl'::hl')) AbsEmpty vars''.
  (*| PECellNi : forall l v l' v' vars vars' vars'' limit1 limit2 eq1 eq2,
               Some vars' = match_expression_ni l l' limit1 limit2 vars eq1 eq2->
               Some vars'' = match_expression v v' limit1 limit2 vars' eq1 eq2 ->
               pickElementNi (AbsCell l' v') vars limit1 limit2 eq1 eq2 (AbsCell l v) (AbsCell l' v') AbsEmpty vars''.*)
Ltac solvePickElementNi :=
     solve [(eapply PEComposeLeftNi;solvePickElementNi) |
            (eapply PEComposeRightNi;solvePickElementNi) |
            ((eapply PEAllNi);[ (simpl;reflexivity) | (simpl;reflexivity) | (simpl;reflexivity)]) |
            ((eapply PEExistsNi);[ (simpl;reflexivity) | (simpl;reflexivity) | (simpl;reflexivity)]) |
            ((eapply PEEachNi);[ (simpl;reflexivity) | (simpl;reflexivity) | (simpl;reflexivity)]) |
            ((eapply PERNi);[ (simpl;reflexivity) | (simpl;reflexivity) | (simpl;reflexivity) ]) ].

(*
 * Pick out two AbsLeaf terms from two AbsState assertions that match.
 *
 * Parameters:
 *   #1 : absState - first state to pick an element out of
 *   #2 : absState - second state to pick an element out of
 *   #3 : list (nat * nat) - bound variable mappings (used in match_state)
 *   #4 : limit1 - limit1 for match_state
 *   #5 : limit2 - limit2 for match_state
 *   #6 : list (list absExp) - equiv1 used in match_state
 *   #7 : list (list absExp) - equiv2 used in match_state
 *   #8 : id - i parameter of the two AbsLeaf parameters picked out
 *   #9 : list (absExp) - list of absExp terms of absLeaf picked out of first state
 *   #10 : list (absExp) - list of absExp terms of absLeaf picked out of second state
 *   #11 : absState - remainder of first term (with picked out element removed)
 *   #12 : absState - remainder of second term (with picked out element removed)
 *   #13 : list (list nat) - returned pairs (with additional pairs from match_state)
 *)
Inductive pick2Rs {ev} {eq} {f} {t} {ac}: @absState ev eq f t ac ->
                                                               @absState ev eq f t ac ->
                                                               list (nat * nat) -> nat -> nat -> 
                                                               list (list (@absExp ev eq f)) ->
                                                               list (list (@absExp ev eq f)) ->
                                                               id ->
                                                               list (@absExp ev eq f) ->
                                                               list (@absExp ev eq f) ->
                                                               @absState ev eq f t ac ->
                                                               @absState ev eq f t ac ->
                                                               list (nat * nat) -> Prop :=
  | P2RComposeFirstLeft : forall a r b c d e ff g h i j k l m,
          pick2Rs a b c d e ff g h i j k l m ->
          pick2Rs (AbsStar a r) b c d e ff g h i j (AbsStar k r) l m
  | P2RComposeFirstRight : forall ll a b c d e ff g h i j k l m,
          pick2Rs a b c d e ff g h i j k l m ->
          pick2Rs (AbsStar ll a) b c d e ff g h i j (AbsStar ll k) l m
  | P2RPick: forall i l1 l2 b b' vars vars' limit1 limit2 eq1 eq2,
          pickElement b vars limit1 limit2 eq1 eq2 (AbsLeaf i l1) (AbsLeaf i l2) b' vars' ->
          pick2Rs (AbsLeaf i l1) b vars limit1 limit2 eq1 eq2 i l1 l2 AbsEmpty b' vars'.

Ltac solvePick2Rs :=
    solve [ (apply P2RComposeFirstLeft;solvePick2Rs) ||
            (apply P2RComposeFirstRight;solvePick2Rs) ||
            (apply P2RPick;solvePickElement) ].


(*
 * Pick out two AbsLeaf (or AbsAll) terms from two AbsState assertions that match.  Note
 * that pickElementNi is used to cause no pairs to be added for either AbsAll or the first
 * parameter given to AbsTree
 *
 * Parameters:
 *   #1 : absState - first state to pick an element out of
 *   #2 : absState - second state to pick an element out of
 *   #3 : list (nat * nat) - bound variable mappings (used in match_state)
 *   #4 : limit1 - limit1 for match_state
 *   #5 : limit2 - limit2 for match_state
 *   #6 : list (list absExp) - equiv1 used in match_state
 *   #7 : list (list absExp) - equiv2 used in match_state
 *   #8 : absExp - term picked out of first state
 *   #9 : absExp - term picked out of second state
 *   #10 : absState - remainder of first term (with picked out element removed)
 *   #11 : absState - remainder of second term (with picked out element removed)
 *   #12 : list (list nat) - returned pairs (with additional pairs from match_state)
 *)
Inductive pick2RsNi {ev} {eq} {f} {t} {ac}: @absState ev eq f t ac ->
                                                                 @absState ev eq f t ac ->
                                                                 list (nat * nat) -> nat -> nat -> 
                                                                 list (list (@absExp ev eq f)) ->
                                                                 list (list (@absExp ev eq f)) ->
                                                                 @absState ev eq f t ac ->
                                                                 @absState ev eq f t ac ->
                                                                 @absState ev eq f t ac ->
                                                                 @absState ev eq f t ac ->
                                                                 list (nat * nat) -> Prop :=
  | P2RComposeFirstLeftNi : forall a r b c d e g h i j k l m,
          pick2RsNi a b c d e g h i j k l m ->
          pick2RsNi (AbsStar a r) b c d e g h i j (AbsStar k r) l m
  | P2RComposeFirstRightNi : forall ll a b c d e g h i j k l m,
          pick2RsNi a b c d e g h i j k l m ->
          pick2RsNi (AbsStar ll a) b c d e g h i j (AbsStar ll k) l m
  | P2RPickNi: forall i l1 l2 b b' vars vars' limit1 limit2 eq1 eq2,
          pickElementNi b vars limit1 limit2 eq1 eq2 (AbsLeaf i l1) (AbsLeaf i l2) b' vars' ->
          pick2RsNi (AbsLeaf i l1) b vars limit1 limit2 eq1 eq2 (AbsLeaf i l1) (AbsLeaf i l2) AbsEmpty b' vars'
  | P2RPickNiAll: forall i l1 l2 b b' vars vars' limit1 limit2 eq1 eq2 i2,
          pickElementNi b vars limit1 limit2 eq1 eq2 (AbsAll i l1) (AbsAll i2 l2) b' vars' ->
          pick2RsNi (AbsAll i l1) b vars limit1 limit2 eq1 eq2 (AbsAll i l1) (AbsAll i2 l2) AbsEmpty b' vars'
  | P2RPickNiExists: forall i l1 l2 b b' vars vars' limit1 limit2 eq1 eq2 i2,
          pickElementNi b vars limit1 limit2 eq1 eq2 (AbsExists i l1) (AbsExists i2 l2) b' vars' ->
          pick2RsNi (AbsExists i l1) b vars limit1 limit2 eq1 eq2 (AbsExists i l1) (AbsExists i2 l2) AbsEmpty b' vars'
  | P2RPickNiEach: forall i l1 l2 b b' vars vars' limit1 limit2 eq1 eq2 i2,
          pickElementNi b vars limit1 limit2 eq1 eq2 (AbsEach i l1) (AbsEach i2 l2) b' vars' ->
          pick2RsNi (AbsEach i l1) b vars limit1 limit2 eq1 eq2 (AbsEach i l1) (AbsEach i2 l2) AbsEmpty b' vars'.

Ltac solvePick2RsNi :=
    solve [ (apply P2RComposeFirstLeftNi;solvePick2RsNi) ||
            (apply P2RComposeFirstRightNi;solvePick2RsNi) ||
            (apply P2RPickNi;solvePickElementNi) ||
            (eapply P2RPickNiAll;solvePickElementNi) ||
            (eapply P2RPickNiExists;solvePickElementNi) ||
            (eapply P2RPickNiEach;solvePickElementNi) ].

Fixpoint pickElementNiF {ev} {eq} {f} {t} {ac}
                        (x : @absState ev eq f t ac) (r : @absState ev eq f t ac)
                        (mapping : list (nat * nat)) (limit1 : nat) (limit2 : nat)
                        (equal_l : list (list (@absExp ev eq f))) (equal_r : list (list (@absExp ev eq f))) :
                        option ((@absState ev eq f t ac) * (@absState ev eq f t ac) *
                                (@absState ev eq f t ac) *
                                (@absState ev eq f t ac) * (list (nat * nat))) :=
    match r with
    | (a ** b) =>
        match pickElementNiF x a mapping limit1 limit2 equal_l equal_r with
        | Some (s1,s2,t1,t2,p) => Some (s1,s2**b,t1,t2,p)
        | None =>
           match pickElementNiF x b mapping limit1 limit2 equal_l equal_r with
           | Some (s1,s2,t1,t2,p) => Some (s1,a**s2,t1,t2,p)
           | None => None
           end
        end
    | AbsEmpty => None
    | (AbsLeaf i2 (f2::r2)) =>
        match x with
        | (AbsLeaf i1 (f1::r1)) =>
            if beq_id i1 i2 then
                match match_expression_ni equal_l equal_r limit1 limit2 f1 f2 mapping with
                | None => None
                | Some (pairs,ff1,ff2) =>
                   match (pair_apply (match_expression equal_l equal_r limit1 limit2) pairs r1 r2) with
                   | None => None
                   | Some (pairs,rr1,rr2) =>
                       match build_leaf (Some (pairs, (ff1::rr1), (ff2::rr2))) i1 with
                       | Some (p,t1,t2) => Some (AbsEmpty,AbsEmpty,t1,t2,pairs)
                       | None => None
                       end
                   end
                end
            else None
        | _ => None
        end
    | y => match match_state_ni limit1 limit2 mapping equal_l equal_r x y with
           | None => None
           | Some (p,t1,t2) => Some (AbsEmpty,AbsEmpty,t1,t2,p)
           end
    end.

Fixpoint pick2RsNiF {ev} {eq} {f} {t} {ac}
                    (l : @absState ev eq f t ac) (r : @absState ev eq f t ac)
                    (mapping : list (nat * nat)) (limit1 : nat) (limit2 : nat)
                    (equal_l : list (list (@absExp ev eq f))) (equal_r : list (list (@absExp ev eq f))) :
                    option ((@absState ev eq f t ac) * (@absState ev eq f t ac) * (@absState ev eq f t ac) *
                            (@absState ev eq f t ac) * (list (nat * nat))) :=
    match l with
    | (a ** b) =>
        match pick2RsNiF a r mapping limit1 limit2 equal_l equal_r with
        | Some (s1,s2,t1,t2,p) => Some (s1**b,s2,t1,t2,p)
        | None => match pick2RsNiF b r mapping limit1 limit2 equal_l equal_r with
                  | Some (s1,s2,t1,t2,p) => Some (a**s1,s2,t1,t2,p)
                  | None => None
                  end
        end
    | AbsEmpty => None
    | x => pickElementNiF x r mapping limit1 limit2 equal_l equal_r
    end.

(*
 * Test whether an absState has only predicates left--nothing allocating heap space
 *)
Inductive allPredicates {ev} {eq} {f} {t} {ac} : @absState ev eq f t ac -> Prop :=
   | APCompose : forall a b,
        allPredicates a ->
        allPredicates b ->
        allPredicates (a ** b)
   | APOrCompose : forall a b,
        allPredicates a ->
        allPredicates b ->
        allPredicates (a *\/* b)
   | APPredicate : forall p, allPredicates ([p])
   | APEmpty : allPredicates AbsEmpty
   | APAccumulate : forall i a b c, allPredicates (AbsAccumulate i a b c)
   | APAll : forall ttt p,
             allPredicates p ->
             allPredicates (AbsAll ttt p)
   | APExistsT : forall p,
                allPredicates p ->
                allPredicates (AbsExistsT p)
   | APExists : forall ttt p,
                allPredicates p ->
                allPredicates (AbsExists ttt p)
   | APEach : forall ttt p,
              allPredicates p ->
              allPredicates (AbsEach ttt p).


Ltac solveAllPredicates := repeat (eapply APCompose || eapply APOrCompose || eapply APEmpty || eapply APAll || eapply APExists || eapply APExistsT || eapply APAccumulate ||eapply APPredicate || eapply APEach).

Fixpoint remove_top_existentials {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) : ((@absState ev eq f t ac) * nat) :=
    match s with
    | AbsExists l s' => match remove_top_existentials s' with
                          | (s,ln) => (s,(S ln))
                          end
    | AbsExistsT s' => match remove_top_existentials s' with
                       | (s,ln) => (s,(S ln))
                       end
    | _ => (s,0)
    end.

Fixpoint restore_top_existentials {ev} {eq} {f} {t} {ac} (s : @absState ev eq f t ac) (n : nat) : @absState ev eq f t ac :=
    match n with
    | 0 => s
    | S n1 => AbsExistsT (restore_top_existentials s n1)
    end.




