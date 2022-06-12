From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
From Coq Require Import PeanoNat.
From Coq Require Import Arith.Le Arith.Plus.
From Coq Require Import Relations.Relation_Definitions Relations.Relation_Operators.
From Coq Require Import ssreflect.

Inductive term : Type :=
  | ttrue                         : term
  | tfalse                        : term
  | tZ                            : term
  | tsucc (t1 : term)             : term
  | tpred (t1 : term)             : term
  | tiszero (t1 : term)           : term
  | tifthenelse (t1 t2 t3 : term) : term.

Proposition term_dec : forall x y : term, {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Definition term_set_add (t : term) (s : set term) : set term :=
  set_add term_dec t s.

Lemma term_set_add_le_cons : forall (t : term) (s : set term),
  length (term_set_add t s) <= length (t :: s).
Proof. 
  intros t s.
  induction s.
  - simpl. apply le_n.
  - simpl.
    destruct (term_dec t a).
    + simpl. apply le_S. apply le_n.
    + simpl in *. apply le_n_S. apply IHs.
Qed.

Definition term_set_union (s1 s2 : set term) : set term :=
  set_union term_dec s1 s2.

Lemma term_set_union_le_append : forall (s1 s2 : set term),
  length (term_set_union s1 s2) <= length (s1 ++ s2).
Proof.
  intros s1 s2.
  induction s2.
  - unfold term_set_union. unfold set_union.
    rewrite app_nil_r. apply le_n.
  - simpl.
    rewrite app_length in IHs2.
    rewrite app_length.
    simpl. rewrite Nat.add_succ_r.
    apply le_trans with (length (a :: term_set_union s1 s2)).
    + apply term_set_add_le_cons.
    + simpl. apply le_n_S. apply IHs2.
Qed.

Lemma term_set_union_length_le : forall (s1 s2 : set term) (n1 n2 : nat),
  length s1 <= n1 -> length s2 <= n2 -> length (term_set_union s1 s2) <= n1 + n2.
Proof.
  intros s1 s2 n1 n2 Hle1 Hle2.
  apply le_trans with (length (s1 ++ s2)).
  - apply term_set_union_le_append.
  - rewrite app_length.
    apply Nat.add_le_mono; assumption.
Qed.

Fixpoint consts (t : term) : set term :=
  match t with
  | tsucc t1 => consts t1
  | tpred t1 => consts t1
  | tiszero t1 => consts t1
  | tifthenelse t1 t2 t3 => 
      term_set_union (consts t1) (term_set_union (consts t2) (consts t3))
  | c => term_set_add c (empty_set term)
  end.

Fixpoint size (t : term) : nat :=
  match t with
  | tsucc t1 => S (size t1)
  | tpred t1 => S (size t1)
  | tiszero t1 => S (size t1)
  | tifthenelse t1 t2 t3 => S (size t1 + size t2 + size t3)
  | _ => 1
  end.

Fixpoint depth (t : term) : nat :=
  match t with
  | tsucc t1 => S (depth t1)
  | tpred t1 => S (depth t1)
  | tiszero t1 => S (depth t1)
  | tifthenelse t1 t2 t3 => S (max (depth t1) (max (depth t2) (depth t3)))
  | _ => 1
  end.

(* 3.3.3 *)
Lemma consts_leq_size : forall t : term, length (consts t) <= size t.
Proof.
  intros t.
  induction t; try (apply le_S; assumption); auto.
  simpl.
  apply le_S.
  rewrite <- plus_assoc.
  apply term_set_union_length_le; try assumption.
  apply term_set_union_length_le; assumption.
Qed.

Inductive value_b : term -> Prop :=
  | V_true  : value_b ttrue
  | V_false : value_b tfalse.

Proposition value_b_dec : forall (t : term), { value_b t } + { ~(value_b t) }.
Proof.
  intros t.
  induction t; 
  try (left; constructor);
  try (right; intros contra; inversion contra).
Qed.

Inductive value_n : term -> Prop :=
  | V_Z               : value_n tZ
  | V_succ (t : term) : value_n t -> value_n (tsucc t).

Proposition value_n_dec : forall (t : term), {value_n t} + {~(value_n t)}.
Proof.
  intros t.
  induction t; 
  try (by (left; constructor));
  try (by (right; intros contra; inversion contra)).
  destruct IHt as [H_tval|H_tnotval].
  - left. apply V_succ. apply H_tval.
  - right. intros contra. inversion contra.
    apply H_tnotval. apply H0.
Qed.

Inductive value : term -> Prop :=
  | V_bool (t : term) : value_b t -> value t
  | V_nat (t : term) : value_n t -> value t.

Proposition value_dec : forall (t : term), {value t} + {~(value t)}.
Proof.
  intros t.
  destruct (value_b_dec t).
  - left. apply V_bool. apply v.
  - destruct (value_n_dec t).
    + left. apply V_nat. apply v.
    + right. intros contra. inversion contra; subst.
      * apply (n H).
      * apply (n0 H).
Qed.

Reserved Notation "t '==>' v" (at level 90, left associativity).
Inductive evalR : relation term :=
  | E_IfTrue : forall (t2 t3 : term),
      tifthenelse ttrue t2 t3 ==> t2
  | E_IfFalse : forall (t2 t3 : term),
      tifthenelse tfalse t2 t3 ==> t3
  | E_If : forall (t1 t2 t3 t1' : term),
      t1 ==> t1' ->
      tifthenelse t1 t2 t3 ==> tifthenelse t1' t2 t3
  | E_Succ : forall (t1 t1' : term),
      t1 ==> t1' ->
      tsucc t1 ==> tsucc t1'
  | E_PredZ : tpred tZ ==> tZ
  | E_PredSucc : forall (t1 : term), 
      value_n t1 ->
      tpred (tsucc t1) ==> t1
  | E_Pred : forall (t1 t1' : term),
      t1 ==> t1' ->
      tpred t1 ==> tpred t1'
  | E_IszeroZ : tiszero tZ ==> ttrue
  | E_IszeroSucc : forall (t1 : term),
      value_n t1 ->
      tiszero (tsucc t1) ==> tfalse
  | E_Iszero : forall (t1 t1' : term),
      t1 ==> t1' ->
      tiszero t1 ==> tiszero t1'
  where "t '==>' v" := (evalR t v) : type_scope.

(* 3.5.6 *)
Definition normal_form (t : term) : Prop := ~(exists t', t ==> t').

Lemma value_b_is_normal_form : forall (t : term),
  value_b t -> normal_form t.
Proof.
  unfold normal_form.
  intros t H_tval [t' H_tt'].
  inversion H_tval; subst; inversion H_tt'.
Qed.

Lemma value_n_is_normal_form : forall (t : term),
  value_n t -> normal_form t.
Proof.
  unfold normal_form.
  intros t H_tval.
  induction H_tval; intros [t' H_tt']; inversion H_tt'; subst.
  apply IHH_tval. exists t1'. apply H0.
Qed.

(* 3.5.7 *)
Theorem value_is_normal_form : forall (t : term),
  value t -> normal_form t.
Proof.
  intros t [|].
  - apply value_b_is_normal_form. assumption.
  - apply value_n_is_normal_form. assumption.
Qed.

(* 3.5.4 *)
Theorem evalR_deterministic : forall (t t' t'' : term),
  t ==> t' -> t ==> t'' -> t' = t''.
Proof.
  intros t t' t'' H_tt'. generalize dependent t''.
  induction H_tt'; intros t'' H_tt''.
  - inversion H_tt''; try reflexivity; subst.
    inversion H3.
  - inversion H_tt''; try reflexivity; subst.
    inversion H3.
  - inversion H_tt''; subst.
    + inversion H_tt'.
    + inversion H_tt'.
    + f_equal.
      apply IHH_tt'. apply H3.
  - inversion H_tt''. subst.
    f_equal. apply IHH_tt'. apply H0.
  - inversion H_tt''; try reflexivity; subst.
    inversion H0.
  - inversion H; subst.
    + inversion H_tt''; try reflexivity; subst.
      exfalso. apply value_n_is_normal_form with (tsucc tZ).
      * apply V_succ. apply H.
      * exists t1'. apply H1.
    + inversion H_tt''; try reflexivity; subst.
      exfalso. apply value_n_is_normal_form with (tsucc (tsucc t)).
      * repeat apply V_succ. apply H0.
      * exists t1'. apply H2.
  - inversion H_tt''; subst.
    + inversion H_tt'.
    + inversion H0; subst.
      * inversion H_tt'; subst. inversion H1.
      * inversion H_tt'; subst.
        exfalso. apply value_n_is_normal_form with (tsucc t).
        -- apply V_succ. apply H.
        -- exists t1'0. apply H2.
    + f_equal. apply IHH_tt'. apply H0.
  - inversion H_tt''; try reflexivity; subst.
    inversion H0.
  - inversion H_tt''; try reflexivity; subst.
    exfalso. apply value_n_is_normal_form with (tsucc t1).
    + apply V_succ. apply H.
    + exists t1'. apply H1.
  - inversion H_tt''; subst.
    + inversion H_tt'.
    + exfalso. apply value_n_is_normal_form with (tsucc t0).
      * apply V_succ. apply H0.
      * exists t1'. apply H_tt'.
    + f_equal. apply IHH_tt'. apply H0.
Qed.

(* Not true with nats:
Theorem normal_form_is_value : forall (t : term),
  normal_form t -> value t.
Proof.
  unfold normal_form.
  intros t.
  induction t; intros H_noexist.
  - apply V_bool. apply V_true.
  - apply V_bool. apply V_false.
  - apply V_nat. apply V_Z.
  - remember (tsucc t) as tsucct.
    apply V_nat. apply V_succ.
Admitted. 
*)

(* 3.5.9 *)
Definition evalR_multi : relation term := clos_refl_trans_1n term evalR.
Notation "t '==>*' v" := (evalR_multi t v) 
  (at level 90, left associativity) : type_scope.

Theorem rt1n_trans_general : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> 
  clos_refl_trans_1n A R y z -> 
  clos_refl_trans_1n A R x z.
Proof.
  intros A R x y z Hxy Hyz.
  induction Hxy.
  - assumption.
  - apply rt1n_trans with y.
    + assumption.
    + apply IHHxy. assumption.
Qed.

Theorem rt1n_step : forall (A : Type) (R : relation A) (x y : A),
  R x y -> clos_refl_trans_1n A R x y.
Proof.
  intros A R x y Hxy.
  apply rt1n_trans with y. assumption. apply rt1n_refl.
Qed.

Theorem rtn1_trans_general : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans_n1 A R x y -> 
  clos_refl_trans_n1 A R y z -> 
  clos_refl_trans_n1 A R x z.
Proof.
  intros A R x y z Hxy Hyz.
  induction Hyz.
  - assumption.
  - apply rtn1_trans with y0; assumption.
Qed.

Theorem rtn1_step : forall (A : Type) (R : relation A) (x y : A),
  R x y -> clos_refl_trans_n1 A R x y.
Proof.
  intros A R x y Hxy.
  apply rtn1_trans with x. assumption. apply rtn1_refl.
Qed.

Theorem rt1n_iff_rtn1 : forall (A : Type) (R : relation A) (x y : A),
  clos_refl_trans_1n A R x y <-> clos_refl_trans_n1 A R x y.
Proof.
  intros A R x y.
  split.
  - intros Hxy.
    induction Hxy.
    + apply rtn1_refl.
    + apply rtn1_trans_general with y.
      * apply rtn1_step. assumption.
      * assumption.
  - intros Hxy.
    induction Hxy.
    + apply rt1n_refl.
    + apply rt1n_trans_general with y.
      * assumption.
      * apply rt1n_step. assumption.
Qed.

(* 3.5.11 *)
Theorem normal_form_unique : forall (t u u' : term),
  normal_form u -> normal_form u' -> t ==>* u -> t ==>* u' -> u = u'.
Proof.
  intros t u u' H_normu H_normu' H_tu H_tu'.
  induction H_tu; subst.
  - inversion H_tu'; subst.
    + reflexivity.
    + exfalso. apply H_normu. exists y. apply H.
  - apply (IHH_tu H_normu).
    inversion H_tu'; subst.
    + exfalso. apply H_normu'. exists y. apply H.
    + replace y with y0. apply H1.
      apply evalR_deterministic with x; assumption.
Qed.

Lemma succ_inner_reduces : forall (t t' : term),
  t ==>* t' -> 
  tsucc t ==>* tsucc t'.
Proof.
  intros t t' Htt'.
  induction Htt'. apply rt1n_refl.
  apply rt1n_trans with (tsucc y); try (apply E_Succ); assumption.
Qed.

Lemma pred_inner_reduces : forall (t t' : term),
  t ==>* t' -> 
  tpred t ==>* tpred t'.
Proof.
  intros t t' Htt'.
  induction Htt'. apply rt1n_refl.
  apply rt1n_trans with (tpred y); try (apply E_Pred); assumption.
Qed.

Lemma iszero_inner_reduces : forall (t t' : term),
  t ==>* t' -> 
  tiszero t ==>* tiszero t'.
Proof.
  intros t t' Htt'.
  induction Htt'. apply rt1n_refl.
  apply rt1n_trans with (tiszero y); try (apply E_Iszero); assumption.
Qed.

Lemma ifthenelse_inner_reduces : forall (t1 t1' t2 t3 : term),
  t1 ==>* t1' ->
  tifthenelse t1 t2 t3 ==>* tifthenelse t1' t2 t3.
Proof.
  intros t1 t1' t2 t3 Ht1t1'.
  induction Ht1t1'. apply rt1n_refl.
  apply rt1n_trans with (tifthenelse y t2 t3); try (apply E_If); assumption.
Qed.

Lemma succ_inner_normal_form : forall (t : term),
  normal_form (tsucc t) ->
  normal_form t.
Proof.
  intros t Hnorm [t' Htt'].
  apply Hnorm. 
  exists (tsucc t'). apply E_Succ. assumption.
Qed.

Lemma pred_inner_normal_form : forall (t : term),
  normal_form (tpred t) ->
  normal_form t.
Proof.
  intros t Hnorm [t' Htt'].
  apply Hnorm. 
  exists (tpred t'). apply E_Pred. assumption.
Qed.

Lemma iszero_inner_normal_form : forall (t : term),
  normal_form (tiszero t) ->
  normal_form t.
Proof.
  intros t Hsuccnorm [t' Htt'].
  apply Hsuccnorm. 
  exists (tiszero t'). apply E_Iszero. assumption.
Qed.

Lemma ifthenelse_inner_normal_form : forall (t1 t2 t3 : term),
  normal_form (tifthenelse t1 t2 t3) ->
  normal_form t1.
Proof.
  intros t1 t2 t3 Hnorm [t1' Ht1t1'].
  apply Hnorm. 
  exists (tifthenelse t1' t2 t3). apply E_If. assumption.
Qed.

(* 3.5.12 *)
Theorem evalR_terminates : forall (t : term),
  exists (t' : term), normal_form t' /\ (t ==>* t').
Proof.
  intros t.
  induction t.
  - exists ttrue. split. 
    + apply value_b_is_normal_form. apply V_true. 
    + apply rt1n_refl.
  - exists tfalse. split. 
    + apply value_b_is_normal_form. apply V_false. 
    + apply rt1n_refl.
  - exists tZ. split. 
    + apply value_n_is_normal_form. apply V_Z. 
    + apply rt1n_refl.
  - destruct IHt as [t' [H_normt' H_tt']].
    exists (tsucc t'). split.
    + intros [t'' H_tsucct't''].
      inversion H_tsucct't''; subst.
      apply H_normt'. exists t1'. apply H0.
    + apply succ_inner_reduces. assumption.
  - destruct IHt as [t' [H_normt' H_tt']].
    assert (Hreduce : tpred t ==>* tpred t').
    { apply pred_inner_reduces. assumption. }
    destruct (value_n_dec t').
    + inversion v; subst.
      * exists tZ. split.
        -- apply value_n_is_normal_form. apply v.
        -- apply rt1n_trans_general with (tpred tZ). assumption.
           apply rt1n_step. apply E_PredZ.
      * exists t0. split.
        -- inversion v. apply value_n_is_normal_form. apply H.
        -- apply rt1n_trans_general with (tpred (tsucc t0)).
           ++ apply pred_inner_reduces. assumption.
           ++ apply rt1n_step. apply E_PredSucc. assumption. 
    + exists (tpred t'). split.
      * intros [t'' Htt''].
         inversion Htt''; subst.
         -- apply n. apply V_Z.
         -- apply n. apply V_succ. apply H0.
         -- apply H_normt'. exists t1'. apply H0.
      * apply pred_inner_reduces. assumption.
  - destruct IHt as [t' [H_normt' H_tt']].
    assert (Hreduce : tiszero t ==>* tiszero t').
    { apply iszero_inner_reduces. assumption. }
    destruct (value_n_dec t').
    + inversion v; subst.
      * exists ttrue. split. apply value_b_is_normal_form. apply V_true.
        apply rt1n_trans_general with (tiszero tZ). assumption.
        apply rt1n_step. apply E_IszeroZ.
      * exists tfalse. split. apply value_b_is_normal_form. apply V_false.
        apply rt1n_trans_general with (tiszero (tsucc t0)). assumption.
        apply rt1n_step. apply E_IszeroSucc. assumption.
    + exists (tiszero t'). split.
      * intros [t'' Htt''].
        inversion Htt''; subst; try (by (apply n; constructor; assumption)).
        apply H_normt'. exists t1'. assumption.
      * assumption.
  - destruct IHt1 as [t1' [Hnormt1' Ht1t1']].
    destruct IHt2 as [t2' [Hnormt2' Ht2t2']].
    destruct IHt3 as [t3' [Hnormt3' Ht3t3']].
    assert (Hreduce : tifthenelse t1 t2 t3 ==>* tifthenelse t1' t2 t3).
    { apply ifthenelse_inner_reduces. assumption. }
    destruct (value_b_dec t1').
    + inversion v; subst.
      * exists t2'. split. assumption.
        apply rt1n_trans_general with (tifthenelse ttrue t2 t3). assumption.
        apply rt1n_trans_general with t2. apply rt1n_step. apply E_IfTrue.
        assumption.
      * exists t3'. split. assumption.
        apply rt1n_trans_general with (tifthenelse tfalse t2 t3). assumption.
        apply rt1n_trans_general with t3. apply rt1n_step. apply E_IfFalse.
        assumption.
    + exists (tifthenelse t1' t2 t3). split.
      * intros [t'' Htt''].
        inversion Htt''; subst; try (by (apply n; constructor; assumption)).
        apply Hnormt1'. exists t1'0. assumption.
      * assumption.
Qed.

Definition stuck (t : term) : Prop := normal_form t /\ ~(value t).
