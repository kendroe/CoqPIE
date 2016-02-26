(**********************************************************************************
 * The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
 * Traversal of Instruction Code) verification framework
 *
 * Developed by Kenneth Roe
 * For more information, check out www.cs.jhu.edu/~roe
 *
 * Tactics.v
 * This file contains the 'crunch' tactic plus a few auxiliary theorems.
 *
 **********************************************************************************)

Require Export SfLib.
Require Export SfLibExtras.
Require Export Coq.Logic.FunctionalExtensionality.

Theorem or_comm:
    forall a b, (a \/ b) -> (b \/ a).
Proof.
    intros. inversion H. right. apply H0. left. apply H0.
Qed.

Theorem in_dist {t}:
    forall a (x:t) b,
        In x (a++b) -> (In x a) \/ (In x b).
Proof.
    induction a. intros. simpl in H. right. apply H.
    intros. simpl in H. inversion H. simpl. left. left. apply H0.
        simpl.
        assert (In x a0 \/ In x b -> (a = x \/ In x a0) \/ In x b).
            intros. inversion H1. left. right. apply H2. right. apply H2.
        apply H1. apply IHa. apply H0.
Qed.

Theorem in_split {t} :
    forall {x:t} l1 l2, In x l1 \/ In x l2 -> In x (l1++l2).
Proof.
    induction l1.
        intros. inversion H. inversion H0. simpl. apply H0.

        intros. simpl in *.
        assert (forall a b c, (a \/ b) \/ c -> a \/ (b \/ c)).
        intros. inversion H0. inversion H1. left. apply H2. right. left. apply H2.
        right. right. apply H1.
        apply H0 in H. inversion H. left. apply H1. right. apply IHl1. apply H1.
Qed.

Fixpoint subset {t} (a : list t) (b : list t) :=
    match a with
    | nil => True
    | (x::y) => In x b /\ subset y b
    end.

Theorem orComm :
    forall a b c, (a \/ b) \/ c -> a \/ (b \/ c).
Proof.
    intros. inversion H. inversion H0. left. apply H1. right. left. apply H1.
    right. right. apply H0.
Qed.

Theorem subsetAppend {t} :
    forall (l : list t) (a : list t), subset l (a++l).
        induction l.
            intros. unfold subset. apply I.

            intros. unfold subset. fold (@subset t).
            split.

            apply in_split. right. simpl. left. reflexivity.
 
            assert (forall (a:list t) (b:list t) (c:t),
                       (a++c::b)=(a++(c::nil))++b).
                induction a1. simpl. reflexivity.
                simpl. intros. rewrite IHa1. reflexivity.
            assert (forall (x : list t), x = (nil++x)). simpl. reflexivity.
            rewrite H. apply IHl.
Qed.

(*
 * Some glue theorems used in unfolding applications
 *)
Theorem or_imply_left1 : forall A B C,
    ((A \/ B) -> C) -> (A -> C).
Proof.
    intros. apply X. left. apply H.
Qed.

Theorem or_imply_left2 : forall A B C,
    ((A \/ B) -> C) -> (B -> C).
Proof.
    intros. apply X. right. apply H.
Qed.

Ltac crunchStep := match goal with
                   | [ |- _ ] => progress simpl 
                   | [ |- _ ] => progress subst
                   | [ |- _ ] => progress (simpl in *)
                   | [ |- _ < _ ] => progress omega
                   | [ |- _ > _ ] => progress omega
                   | [ |- _ <= _ ] => progress omega
                   | [ |- _ >= _ ] => progress omega

                   | [ |- _ = _ ] => progress reflexivity
                   | [ H: ?X |- ?X ] => apply H
                   | [ |- True ] => apply I
                   | [ H: ?X _ |- ?X _ ] => apply H
                   | [ H: ?X _ _ |- ?X _ _] => apply H
                   | [ H: ?X _ _ _ |- ?X _ _ _] => apply H
                   | [ H: ?X _ _ _ _ |- ?X _ _ _ _] => apply H
                   | [ H: ?X _ _ _ _ _ |- ?X _ _ _ _ _] => apply H
                   | [ H: ?X _ _ _ _ _ _ |- ?X _ _ _ _ _ _] => apply H
                   | [ H: ?X _ _ _ _ _ _ _ |- ?X _ _ _ _ _ _ _] => apply H
                   | [ H: forall _, ?X _ |- ?X _] => apply H
                   | [ H: forall _, ?X _ _ |- ?X _ _] => apply H
                   | [ H: forall _, ?X _ _ _ |- ?X _ _ _] => apply H
                   | [ H: ?X \/ ?Y |- ?Y \/ ?X ] => apply or_comm
                   | [ H: forall _, (?X \/ ?Y) |- ?Y \/ ?X ] => apply or_comm

                   | [ |- ?A = ?A \/ _ ] => (left;reflexivity)
                   | [ |- _ \/ ?A = ?A ] => (right;reflexivity)
                   | [ |- _ \/ ?A = ?A \/ _] => (right;left;reflexivity)
                   | [ |- _ \/ _ \/ ?A = ?A] => (right;right;reflexivity)

                   | [ H: ?A |- ?A \/ _ ] => (left;apply H)
                   | [ H: ?A |- _ \/ ?A ] => (right;apply H)
                   | [ H: ?A |- _ \/ ?A \/ _] => (right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ ?A] => (right;right;apply H)
                   | [ H: ?A |- _ \/ _ \/ ?A \/ _] => (right;right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ ?A] => (right;right;right;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ ?A \/ _] => (right;right;right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ ?A] => (right;right;right;right;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ ?A \/ _] => (right;right;right;right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ _ \/ ?A] => (right;right;right;right;right;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ _ \/ ?A \/ _] => (right;right;right;right;right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ ?A] => (right;right;right;right;right;right;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ ?A \/ _] => (right;right;right;right;right;right;left;apply H)
                   | [ H: ?A |- _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ ?A] => (right;right;right;right;right;right;right;apply H)

                   | [ |- _ /\ _ ] => split
                   | [ |- _ <-> _ ] => split

                   | [ H: true = false |- _ ] => inversion H
                   | [ H: false = true |- _ ] => inversion H
                   | [ H: Some _ = None |- _ ] => inversion H
                   | [ H: In _ nil |- _ ] => inversion H
                   | [ H: False |- _ ] => inversion H
                   | [ H: None = Some _ |- _ ] => inversion H
                   | [ H: ?X <> ?X |- _ ] => elim H

                   | [ |- None <> Some _ ] => let x :=fresh in (intro x;inversion x)
                   | [ |- Some _ <> None ] => let x :=fresh in (intro x;inversion x)

                   | [ H: Some _ = Some _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: (_,_) = (_,_) |- _ ] => (inversion H;subst;clear H)
                   | [ H: (_::_) = (_::_) |- _ ] => (inversion H;subst;clear H)
                   | [ H: _ \/ False |- _ ] => (inversion H;subst;clear H)
                   | [ H: False \/ _ |- _ ] => (inversion H;subst;clear H)

                   | [ H1: Some _ = ?P, H2: Some _ = ?P |- _ ] => rewrite <- H2 in H1
                   | [ H1: Some _ = ?P, H2: ?P = Some _ |- _ ] => rewrite H2 in H1
                   | [ H1: ?P = Some _, H2: Some _ = ?P |- _ ] => rewrite <- H2 in H1
                   | [ H1: ?P = Some _, H2: ?P = Some _ |- _ ] => rewrite H2 in H1
                   | [ H1: None = ?P, H2: Some _ = ?P |- _ ] => rewrite <- H2 in H1
                   | [ H1: None = ?P, H2: ?P = Some _ |- _ ] => rewrite H2 in H1
                   | [ H1: ?P = None, H2: Some _ = ?P |- _ ] => rewrite <- H2 in H1
                   | [ H1: ?P = None, H2: ?P = Some _ |- _ ] => rewrite H2 in H1

                   | [ H: ?A = ?B |- ?B = ?A ] => rewrite H

                   | [ H: _ /\ _ |- _ ] => (inversion H;subst;clear H)
                   | [ H: exists _, _ |- _ ] => (inversion H;subst;clear H)

                   | [ |- (fun _ => _) = (fun _ => _) ] => let x := fresh in extensionality x
                   (*| [ H: ?A=?B |- (?A::_) = (?B::_) ] => rewrite H
                   | [ H: ?B=?A |- (?A::_) = (?B::_) ] => rewrite H
                   | [ H: ?A=?B |- (_::?A) = (_::?B) ] => rewrite H
                   | [ H: ?B=?A |- (_::?A) = (_::?B) ] => rewrite H
                   | [ H: _ -> ?A=?B |- (?A::_) = (?B::_) ] => rewrite H
                   | [ H: _ -> ?B=?A |- (?A::_) = (?B::_) ] => rewrite H
                   | [ H: _ -> ?A=?B |- (_::?A) = (_::?B) ] => rewrite H
                   | [ H: _ -> ?B=?A |- (_::?A) = (_::?B) ] => rewrite H*)

                   | [ H: false = beq_id ?A ?B |- context [if beq_id ?B ?A then _ else _] ] => ((rewrite beq_id_comm);rewrite <- H) | [ H: false = beq_id ?A ?B |- context [if beq_id ?A ?B then _ else _] ] => rewrite <- H
                   | [ H: false = beq_id ?A ?B, H2: context [if beq_id ?B ?A then _ else _] |- _ ] => ((rewrite beq_id_comm in H2);rewrite <- H in H2)
                   | [ H: false = beq_id ?A ?B, H2: context [if beq_id ?A ?B then _ else _] |- _ ] => rewrite <- H in H2

                   | [ HE: ?C = None, H: context [match ?C with Some _ => _ | None => _ end] |- _] => rewrite HE in H
                   | [ HE: None = ?C, H: context [match ?C with Some _ => _ | None => _ end] |- _] => rewrite <- HE in H
                   | [ HE: ?C = None, H: context [match ?C with None => _ | Some _ => _ end] |- _] => rewrite HE in H
                   | [ HE: None = ?C, H: context [match ?C with None => _ | Some _ => _ end] |- _] => rewrite <- HE in H
                   | [ HE: ?C = Some _, H: context [match ?C with Some _ => _ | None => _ end] |- _] => rewrite HE in H
                   | [ HE: Some _ = ?C, H: context [match ?C with Some _ => _ | None => _ end] |- _] => rewrite <- HE in H
                   | [ HE: ?C = Some _, H: context [match ?C with None => _ | Some _ => _ end] |- _] => rewrite HE in H
                   | [ HE: Some _ = ?C, H: context [match ?C with None => _ | Some _ => _ end] |- _] => rewrite <- HE in H
                   | [ HE: ?C = None |- context [match ?C with Some _ => _ | None => _ end] ] => rewrite HE
                   | [ HE: None = ?C |- context [match ?C with Some _ => _ | None => _ end] ] => rewrite <- HE
                   | [ HE: ?C = None |- context [match ?C with None => _ | Some _ => _ end] ] => rewrite HE
                   | [ HE: None = ?C |- context [match ?C with None => _ | Some _ => _ end] ] => rewrite <- HE
                   | [ HE: ?C = Some _ |- context [match ?C with Some _ => _ | None => _ end] ] => rewrite HE
                   | [ HE: Some _ = ?C |- context [match ?C with Some _ => _ | None => _ end] ] => rewrite <- HE
                   | [ HE: ?C = Some _ |- context [match ?C with None => _ | Some _ => _ end] ] => rewrite HE
                   | [ HE: Some _ = ?C |- context [match ?C with None => _ | Some _ => _ end] ] => rewrite <- HE
                   | [ H: true = beq_id _ _ |- _ ] => (apply beq_id_eq in H;subst)

                   | [ |- forall (_ : _), _] => intros
                   | [ |- _ -> _] => intros

                   | [ H: In _ (_++_) |- _ ] => apply in_dist in H
                   | [ |- In _ (_++_) ] => apply in_split
                   end.

Ltac caseAnalysisStep := match goal with
                         | [ H: context [match ?C with None => _ | Some _ => _ end] |- _] => let X := fresh in (remember C as X;destruct X)
                         | [ |- context [if ?C then _ else _]] => let X := fresh in (remember C as X;destruct X)
                         | [ |- context [match ?C with Some _ => _ | None => _ end]] => let X := fresh in (remember C as X;destruct X)
                         | [ |- context [match ?C with None => _ | Some _ => _ end]] => let X := fresh in (remember C as X;destruct X)
                         | [ H: context [match ?C with Some _ => _ | None => _ end] |- _] => let X := fresh in (remember C as X;destruct X)
                         | [ H: context [match ?C with None => _ | Some _ => _ end] |- _] => let X := fresh in (remember C as X;destruct X)
                         | [ H: _ \/ _ |- _] => (inversion H;subst;clear H)
                         end.

Ltac crunch := repeat crunchStep.

Ltac caseAnalysis := (repeat caseAnalysisStep);crunch.
