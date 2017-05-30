(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * AbsStateInstance.v
 * This file contains definitions needed to instantiate the abstract state.
 *
 * Key definitions:
 *    basicEval (used to fill in f parameter of absExp)
 *    basicState (used to fill in the t parameter of absState)
 *    convertToAbsExp (used by forward propagation tactic proofs)
 *    supportsBasicFunctionality - instantiation of supportsFunctionality
 *    absStateBasic - instantiated version of absState with the above
 *
 * This file also contains much of the notation used for display abstract states.
 * There are a few pieces in absState.v
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export ImpHeap.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export AbsState.

(**********************************************************************************
 *
 * Recursive heap declarations
 *
 *
 * This section contains the declarations to build up the definition of Tree
 * which represent the recursively defined heap elements such as trees and linked
 * lists.
 **********************************************************************************)


Ltac simplifyStripNatValues :=
    match goal with
    | [ |- strip_nat_values _ nil] => apply SNVNil
    | [ |- strip_nat_values nil _] => apply SNVNil
    | [ |- strip_nat_values _ (_::_)] => (apply SNVCons);try simplifyStripNatValues
    | [ |- strip_nat_values (_::_) _] => (apply SNVCons);try simplifyStripNatValues
    end.

(*Hint Immediate SNVNil.*)
Hint Constructors strip_nat_values.








(* This function is used in absExecute in defining (and proving) many tactics *)
Fixpoint convertToAbsExp (e : aexp) : absExp :=
  match e with
  | ANum v => AbsConstVal (NatValue v)
  | AVar id => AbsVar id
  | APlus l r => AbsFun (Id 2) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AMinus l r => AbsFun (Id 3) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AMult l r => AbsFun (Id 4) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | AEq l r => AbsFun (Id 5) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALe l r => AbsFun (Id 10) ((AbsFun (Id 6) ((convertToAbsExp r)::(convertToAbsExp l)::nil))::nil)
  | ALand l r => AbsFun (Id 11) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALor l r => AbsFun (Id 12) ((convertToAbsExp l)::(convertToAbsExp r)::nil)
  | ALnot t => AbsFun (Id 10) ((convertToAbsExp t)::nil)
  end.


Notation "'[' x ']'" := (AbsLeaf (Id 101) (x::nil))
  (at level 20).
Notation "x '|->' y" := (AbsLeaf (Id 103) (x::y::nil))
  (at level 20).
Notation "'TREE(' r ',' f ',' s ',' l ')'" := (AbsLeaf (Id 102) (r::f::s::l))
  (at level 20).
Notation "'Path(' r ',' f ',' p ',' s ',' l ')'" := (AbsLeaf (Id 105) (r::f::p::s::l))
  (at level 20).
Notation "'ARRAY(' r ',' s ',' v ')'" := (AbsLeaf (Id 104) (r::s::v::nil))
  (at level 20).




Notation "'SUM(' e ',' f ',' t ')'" := (AbsAccumulate AbsSumId e f t) (at level 20).

(***************************************************************************
 *
 * absStateBasic
 *
 * Instantiated version of absState with 'f' instantiated to basicEval,
 * 't' instantiated to basicState and 'ac' basicAccumulate.  This is the
 * instantiation of AbsState that is useful for our derivation in
 * TreeTraversal.v.  The 'ev' parameter is instantiated to 'unit' and 'eq'
 * is instantiated to a function 'eq_unit' which we define below.
 *
 ***************************************************************************)

(*Definition absExpBasicF {t} {teq} := @absExp t teq (@basicEval t).

Definition absStateBasicF {t} {teq} {f} := @absState t teq f
                                           (@basicState t) (@basicAccumulate t teq f).

Definition unitEval := @basicEval unit.
Opaque unitEval.

Definition eq_unit (a : unit) (b : unit) := true.
Definition absExpBasic := @absExpBasicF unit eq_unit.
Definition absStateBasic := @absState unit eq_unit (@basicEval unit) (@basicState unit) (@basicAccumulate unit eq_unit (@basicEval unit)).*)

(*************************************************************************
 *
 * Notations for the functions defined in basicEval
 *
 *************************************************************************)

Notation "'nth(' d ',' n ')'" := (AbsFun (Id 1) (d::n::nil))
  (at level 3).
(*Definition AbsFieldRef {ev} {eq} {f} := @AbsFun ev eq f AbsFieldRefId.*)
Notation "x '++++' y" := (AbsFun (Id 2) (x::y::nil))
  (at level 4).
(*Definition AbsPlus {ev} {eq} {f} := @AbsFun ev eq f AbsPlusId.*)
Notation "x '----' y" := (AbsFun (Id 3) (x::y::nil))
  (at level 4).
(*Definition AbsMinus {ev} {eq} {f} := @AbsFun ev eq f AbsMinusId.*)
Notation "x '****' y" := (AbsFun (Id 4) (x::y::nil))
  (at level 5).
(*Definition AbsTimes {ev} {eq} {f} := @AbsFun ev eq f AbsTimesId.*)
Notation "x '====' y" := (AbsFun (Id 5) (x::y::nil))
  (at level 6).
(*Definition AbsEqual {ev} {eq} {f} := @AbsFun ev eq f AbsEqualId.*)
Notation "x '<<<<' y" := (AbsFun (Id 6) (x::y::nil))
  (at level 6).
(*Definition AbsLess {ev} {eq} {f} := @AbsFun ev eq f AbsLessId.*)
Notation "x 'inTree' t" := (AbsFun (Id 7) (x::t::nil))
  (at level 5).
(*Definition AbsRMember {ev} {eq} {f} := @AbsFun ev eq f AbsRMemberId.*)
Notation "x 'inTreeLoc' t" := (AbsFun (Id 8) (x::t::nil))
  (at level 5).
(*Definition AbsRInclude {ev} {eq} {f} := @AbsFun ev eq f AbsRIncludeId.*)
Notation "x '-->>' y" := (AbsFun (Id 9) (x::y::nil))
  (at level 10).
(*Definition AbsImply {ev} {eq} {f} := @AbsFun ev eq f AbsImplyId.*)
Notation "'~~' x" := (AbsFun (Id 10) (x::nil))
  (at level 7).
(*Definition AbsNot {ev} {eq} {f} := @AbsFun ev eq f AbsNotId.*)
Notation "x '//\\' y" := (AbsFun (Id 11) (x::y::nil))
  (at level 8).
(*Definition AbsAnd {ev} {eq} {f} := @AbsFun ev eq f AbsAndId.*)
Notation "x '\\//' y" := (AbsFun (Id 12) (x::y::nil))
  (at level 9).
(*Definition AbsOr {ev} {eq} {f} := @AbsFun ev eq f AbsOrId.*)
Notation "'ite(' x ',' y ',' z ')'" := (AbsFun (Id 13) (x::y::z::nil))
  (at level 10).
(*Definition AbsIte {ev} {eq} {f} := @AbsFun ev eq f AbsIteId.*)
Notation "'find(' x ',' y ')'" := (AbsFun (Id 14) (x::y::nil))
  (at level 3).
(*Definition AbsFindRecord {ev} {eq} {f} := @AbsFun ev eq f AbsFindRecordId.*)
Notation "'list(' x ')'" := (AbsFun (Id 15) (x))
  (at level 3).
(*Definition AbsBuildList {ev} {eq} {f} := @AbsFun ev eq f AbsBuildListId.*)
Notation "'TreeRecords(' x ')'" := (AbsFun (Id 16) (x::nil))
  (at level 3).
(*Definition AbsRecordList {ev} {eq} {f} := @AbsFun ev eq f AbsRecordListId.*)
Notation "'range(' x ',' y ')'" := (AbsFun (Id 17) (x::y::nil))
  (at level 3).
(*Definition AbsRangeList {ev} {eq} {f} := @AbsFun ev eq f AbsRangeListId.*)
Notation "'--(' a ',' b ')--->' c" := (AbsFun (Id 1) ((AbsFun (Id 14) (a::b::nil))::(AbsFun (Id 3) (c::#1::nil))::nil))
  (at level 3).
Notation "'--(' a ',' b ')-->' c" := (AbsFun (Id 1) ((AbsFun (Id 14) (a::b::nil))::(AbsConstVal (NatValue (c+1)))::nil))
  (at level 3).
Notation "'replacenth(' d ',' n ',' e ')'" := (AbsFun (Id 18) (d::n::e::nil))
  (at level 3).

(****************************************************************************
 *
 * supportsBasicFunctionality
 *
 * instantiation of supportsFunctionality
 *
 ****************************************************************************)

(*Definition supportsBasicFunctionality v:=
    supportsFunctionality unit eq_unit (@basicEval unit) 18 basicState 4 (@basicAccumulate unit eq_unit (@basicEval unit)) 0
                          ev eq f t ac (fun (x:ev) => tt) (fun x => (v:ev)).*)





















