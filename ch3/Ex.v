From Ch3 Require Export Defns.

From Coq Require Import Relations.Relation_Definitions Relations.Relation_Operators.
From Coq Require Import ssreflect.

(* 3.5.14 *)

Lemma ex_3_5_14 : forall (t t' t'': term), t ==> t' -> t ==> t'' -> t' = t''.
Proof.
  apply evalR_deterministic.
Qed.

(* 3.5.16 *)

Inductive term_w : Type :=
  | twtrue                           : term_w
  | twfalse                          : term_w
  | twZ                              : term_w
  | twsucc (t1 : term_w)             : term_w
  | twpred (t1 : term_w)             : term_w
  | twiszero (t1 : term_w)           : term_w
  | twifthenelse (t1 t2 t3 : term_w) : term_w
  | twwrong                          : term_w.

Inductive term_mapping : term -> term_w -> Prop :=
  | tmtrues       : term_mapping ttrue twtrue
  | tmfalses      : term_mapping tfalse twfalse
  | tmZs          : term_mapping tZ twZ
  | tmsuccs       : forall (t1 : term) (tw1 : term_w),
      term_mapping t1 tw1 ->
      term_mapping (tsucc t1) (twsucc tw1)
  | tmpreds       : forall (t1 : term) (tw1 : term_w),
      term_mapping t1 tw1 ->
      term_mapping (tpred t1) (twpred tw1)
  | tmiszeros     : forall (t1 : term) (tw1 : term_w),
      term_mapping t1 tw1 ->
      term_mapping (tiszero t1) (twiszero tw1)
  | tmifthenelses : forall (t1 t2 t3 : term) (tw1 tw2 tw3 : term_w),
      term_mapping t1 tw1 -> term_mapping t2 tw2 -> term_mapping t3 tw3 ->
      term_mapping (tifthenelse t1 t2 t3) (twifthenelse tw1 tw2 tw3).

Inductive bad_n : term_w -> Prop :=
  | BN_wrong : bad_n twwrong
  | BN_true  : bad_n twtrue
  | BN_false : bad_n twfalse.

Inductive value_b_w : term_w -> Prop :=
  | VW_true  : value_b_w twtrue
  | VW_false : value_b_w twfalse.

Inductive value_n_w : term_w -> Prop :=
  | VW_Z : value_n_w twZ
  | VW_succ (tw : term_w) : value_n_w tw -> value_n_w (twsucc tw).

Proposition value_n_iff_value_n_w : forall (t : term) (tw : term_w),
  term_mapping t tw ->
  value_n t <-> value_n_w tw.
Proof.
  intros t tw Hmap. split.
  - intros Hvalnt. generalize dependent tw.
    induction Hvalnt; intros tw Hmap.
    + inversion Hmap; subst. apply VW_Z.
    + inversion Hmap; subst. apply VW_succ.
      apply IHHvalnt. assumption.
  - intros Hvalntw. generalize dependent t.
    induction Hvalntw; intros t Hmap.
    + inversion Hmap; subst. apply V_Z.
    + inversion Hmap; subst. apply V_succ.
      apply IHHvalntw. assumption.
Qed.

Proposition value_b_w_dec : forall (t : term_w),
  {value_b_w t} + {~(value_b_w t)}.
Proof.
  intros t.
  destruct t eqn:E;
  (by (left; constructor) ||
   by (right; intros contra; inversion contra)).
Qed.

Inductive bad_b : term_w -> Prop :=
  | BB_w                    : bad_b twwrong
  | BB_value_n (t : term_w) : value_n_w t -> bad_b t.

Reserved Notation "t '==>w' v" (at level 90, left associativity).
Inductive evalR_w : relation term_w :=
  | EW_IfTrue : forall (t2 t3 : term_w),
      twifthenelse twtrue t2 t3 ==>w t2
  | EW_IfFalse : forall (t2 t3 : term_w),
      twifthenelse twfalse t2 t3 ==>w t3
  | EW_If : forall (t1 t2 t3 t1' : term_w),
      t1 ==>w t1' ->
      twifthenelse t1 t2 t3 ==>w twifthenelse t1' t2 t3
  | EW_Succ : forall (t1 t1' : term_w),
      t1 ==>w t1' ->
      twsucc t1 ==>w twsucc t1'
  | EW_PredZ : twpred twZ ==>w twZ
  | EW_PredSucc : forall (t1 : term_w), 
      value_n_w t1 ->
      twpred (twsucc t1) ==>w t1
  | EW_Pred : forall (t1 t1' : term_w),
      t1 ==>w t1' ->
      twpred t1 ==>w twpred t1'
  | EW_IszeroZ : twiszero twZ ==>w twtrue
  | EW_IszeroSucc : forall (t1 : term_w),
      value_n_w t1 ->
      twiszero (twsucc t1) ==>w twfalse
  | EW_Iszero : forall (t1 t1' : term_w),
      t1 ==>w t1' ->
      twiszero t1 ==>w twiszero t1'
  | EW_IfWrong : forall (t1 t2 t3 : term_w),
      bad_b t1 ->
      twifthenelse t1 t2 t3 ==>w twwrong
  | EW_SuccWrong : forall (t1 : term_w),
      bad_n t1 ->
      twsucc t1 ==>w twwrong
  | EW_PredWrong : forall (t1 : term_w),
      bad_n t1 ->
      twpred t1 ==>w twwrong
  | EW_IszeroWrong : forall (t1 : term_w),
      bad_n t1 ->
      twiszero t1 ==>w twwrong
  where "t '==>w' v" := (evalR_w t v) : type_scope.

Definition normal_form_w (tw : term_w) : Prop := ~(exists tw', tw ==>w tw').

Theorem value_n_w_is_normal_form_w : forall (tw : term_w),
  value_n_w tw -> normal_form_w tw.
Proof.
  intros tw Hvalntw.
  induction Hvalntw; intros [tw' contra]; inversion contra; subst.
  + apply IHHvalntw. exists t1'. assumption.
  + inversion Hvalntw; subst; inversion H0.
Qed.

Theorem evalR_preserves_mapping : forall (t t' : term) (tw tw' : term_w),
  term_mapping t tw -> t ==> t' -> tw ==>w tw' ->
  term_mapping t' tw'.
Proof.
  intros t t' tw tw' Hmap Hstept Hsteptw. 
  generalize dependent t'. generalize dependent tw'.
  induction Hmap; intros tw' Hsteptw t' Hstept;  try (by (inversion Hsteptw)).
  - inversion Hstept; subst.
    inversion Hsteptw; subst.
    + apply tmsuccs. apply IHHmap; assumption.
    + inversion H1; subst; inversion Hmap; subst; inversion H0.
  - inversion Hsteptw; subst.
    + inversion Hmap; subst. inversion Hstept; subst.
      * apply tmZs.
      * inversion H0.
    + inversion Hmap; subst.
      inversion H0; subst.
      * inversion H2; subst. inversion Hstept; subst.
        -- apply tmZs.
        -- inversion H1; subst. inversion H3.
      * inversion H2; subst. inversion Hstept; subst.
        -- apply tmsuccs. assumption.
        -- exfalso. apply value_n_is_normal_form with (tsucc (tsucc t1)).
           ++ apply V_succ. apply V_succ. 
              rewrite value_n_iff_value_n_w. apply H. apply H4.
           ++ exists t1'. assumption.
    + inversion Hstept; subst.
      * inversion Hmap; subst. inversion H0.
      * inversion Hmap; subst.
        exfalso. apply value_n_w_is_normal_form_w with (twsucc tw0).
        -- apply VW_succ.
           rewrite <- value_n_iff_value_n_w. apply H1. assumption.
        -- exists t1'. assumption.
      * apply tmpreds.
        apply IHHmap; assumption.
    + inversion H0; subst; inversion Hmap; subst;
      inversion Hstept; subst; inversion H1.
  - inversion Hstept; subst.
    + inversion Hmap; subst. inversion Hsteptw; subst; try (by (inversion H0)).
      apply tmtrues.
    + inversion Hmap; subst. inversion Hsteptw; subst.
      * apply tmfalses.
      * exfalso. apply value_n_w_is_normal_form_w with (twsucc tw0).
        -- apply VW_succ. apply value_n_iff_value_n_w with t0; assumption.
        -- exists t1'. assumption.
      * inversion H2.
    + inversion Hsteptw; subst.
      * inversion Hmap; subst. inversion H0.
      * inversion Hmap; subst.
        exfalso. apply value_n_is_normal_form with (tsucc t2).
        -- apply V_succ. apply value_n_iff_value_n_w with t0; assumption.
        -- exists t1'. assumption.
      * apply tmiszeros. apply IHHmap; assumption.
      * inversion H1; subst;
        inversion Hmap; subst; inversion Hstept; subst; inversion H3.
  - inversion Hstept; subst.
    + inversion Hmap1; subst.
      inversion Hsteptw; subst.
      * assumption.
      * inversion H3.
      * inversion H3; subst. inversion H.
    + inversion Hmap1; subst.
      inversion Hsteptw; subst.
      * assumption.
      * inversion H3.
      * inversion H3; subst. inversion H.
    + inversion Hsteptw; subst.
      * inversion Hmap1; subst. inversion H3.
      * inversion Hmap1; subst. inversion H3.
      * apply tmifthenelses;
        (apply IHHmap1; assumption) || assumption.
      * inversion H4; subst.
        -- inversion Hmap1.
        -- inversion H; subst.
           ++ inversion Hmap1; subst. inversion H3.
           ++ exfalso. apply value_n_is_normal_form with t1.
              ** apply value_n_iff_value_n_w with (twsucc tw); assumption.
              ** exists t1'. assumption.
Qed.

Definition evalR_w_multi : relation term_w := clos_refl_trans_1n term_w evalR_w.
Notation "t '==>w*' v" := (evalR_w_multi t v) 
  (at level 90, left associativity) : type_scope.

Lemma succ_w_inner_reduces : forall (tw tw' : term_w),
  tw ==>w* tw' -> 
  twsucc tw ==>w* twsucc tw'.
Proof.
  intros tw tw' Hsteps.
  induction Hsteps. apply rt1n_refl.
  apply rt1n_trans with (twsucc y); try (apply EW_Succ); assumption.
Qed.

Lemma pred_w_inner_reduces : forall (tw tw' : term_w),
  tw ==>w* tw' -> 
  twpred tw ==>w* twpred tw'.
Proof.
  intros tw tw' Hsteps.
  induction Hsteps. apply rt1n_refl.
  apply rt1n_trans with (twpred y); try (apply EW_Pred); assumption.
Qed.

Lemma iszero_w_inner_reduces : forall (tw tw' : term_w),
  tw ==>w* tw' -> 
  twiszero tw ==>w* twiszero tw'.
Proof.
  intros tw tw' Hsteps.
  induction Hsteps. apply rt1n_refl.
  apply rt1n_trans with (twiszero y); try (apply EW_Iszero); assumption.
Qed.

Lemma ifthenelse_w_inner_reduces : forall (tw1 tw1' tw2 tw3 : term_w),
  tw1 ==>w* tw1' -> 
  twifthenelse tw1 tw2 tw3 ==>w* twifthenelse tw1' tw2 tw3.
Proof.
  intros tw1 tw1' tw2 tw3 Hsteps.
  induction Hsteps. apply rt1n_refl.
  apply rt1n_trans with (twifthenelse y tw2 tw3); try (apply EW_If); assumption.
Qed.

Theorem term_mapping_forward : forall (t : term),
  exists (tw : term_w), term_mapping t tw.
Proof.
  intros t.
  induction t; try (by (eexists; constructor)).
  - destruct IHt as [tw Hmap].
    exists (twsucc tw). apply tmsuccs. assumption.
  - destruct IHt as [tw Hmap].
    exists (twpred tw). apply tmpreds. assumption.
  - destruct IHt as [tw Hmap].
    exists (twiszero tw). apply tmiszeros. assumption.
  - destruct IHt1 as [tw1 Hmap1].
    destruct IHt2 as [tw2 Hmap2].
    destruct IHt3 as [tw3 Hmap3].
    exists (twifthenelse tw1 tw2 tw3).
    apply tmifthenelses; assumption.
Qed.

Theorem term_mapping_forward_unique : forall (t : term) (tw tw' : term_w),
  term_mapping t tw -> term_mapping t tw' -> tw = tw'.
Proof.
  intros t tw tw' Hmap1 Hmap2.
  generalize dependent tw'.
  induction Hmap1; intros tw' Hmap2; 
  try (by (
    inversion Hmap2; reflexivity ||
    inversion Hmap2; subst; f_equal; apply IHHmap1; assumption
  )).
  inversion Hmap2; subst. f_equal.
  - apply IHHmap1_1. assumption.
  - apply IHHmap1_2. assumption.
  - apply IHHmap1_3. assumption.
Qed.

Theorem term_mapping_preserves_evalR : forall (t t' : term) (tw tw' : term_w),
  term_mapping t tw -> term_mapping t' tw' -> t ==> t' -> tw ==>w tw'.
Proof.
  intros t t' tw tw' Hmap1 Hmap2 Hstep.
  generalize dependent tw. generalize dependent tw'.
  induction Hstep; intros;
  try (by (
    inversion Hmap1; subst; inversion Hmap2; subst;
    constructor; apply IHHstep; assumption
  )).
  - inversion Hmap1; subst. inversion H2; subst.
    rewrite (term_mapping_forward_unique t2 tw2 tw'); try assumption.
    apply EW_IfTrue.
  - inversion Hmap1; subst. inversion H2; subst.
    rewrite (term_mapping_forward_unique t3 tw3 tw'); try assumption.
    apply EW_IfFalse.
  - inversion Hmap1; subst. inversion Hmap2; subst.
    rewrite (term_mapping_forward_unique t2 tw2 tw4); try assumption.
    rewrite (term_mapping_forward_unique t3 tw3 tw5); try assumption.
    apply EW_If. apply IHHstep; assumption.
  - inversion Hmap1; subst. inversion Hmap2; subst.
    inversion H0. apply EW_PredZ.
  - inversion Hmap1; subst. inversion H1; subst.
    rewrite (term_mapping_forward_unique t1 tw0 tw'); try assumption.
    apply EW_PredSucc.
    apply value_n_iff_value_n_w with t1; assumption.
  - inversion Hmap1; subst. inversion Hmap2; subst. inversion H0; subst.
    apply EW_IszeroZ.
  - inversion Hmap1; subst. inversion Hmap2; subst. inversion H1; subst.
    apply EW_IszeroSucc.
    apply value_n_iff_value_n_w with t1; assumption.
Qed.

Theorem evalR_multi_preserves_mapping : forall (t t' : term) (tw tw' : term_w),
  term_mapping t tw -> term_mapping t' tw' -> t ==>* t' ->
  tw ==>w* tw'.
Proof.
  intros t t' tw tw' Hmap1 Hmap2 Hsteps.
  generalize dependent tw. generalize dependent tw'.
  induction Hsteps; intros tw' Hmap2 tw Hmap1.
  - rewrite (term_mapping_forward_unique _ _ _ Hmap1 Hmap2).
    apply rt1n_refl.
  - destruct (term_mapping_forward y) as [yw Hmapyw].
    apply rt1n_trans with yw.
    + apply term_mapping_preserves_evalR with x y; assumption.
    + apply IHHsteps; assumption.
Qed.

Lemma stuck_implies_wrong_base : forall (t : term) (tw : term_w),
  term_mapping t tw -> stuck t -> tw ==>w* twwrong.
Proof.
  intros t tw Hmap.
  induction Hmap; intros [Hnorm Hnotval].
  - exfalso. apply Hnotval. apply V_bool. apply V_true.
  - exfalso. apply Hnotval. apply V_bool. apply V_false.
  - exfalso. apply Hnotval. apply V_nat. apply V_Z.
  - destruct (value_dec t1).
    + inversion v; subst.
      * apply rt1n_step. apply EW_SuccWrong. 
        inversion H; subst; inversion Hmap; constructor.
      * exfalso. apply Hnotval. apply V_nat. apply V_succ. assumption.
    + apply rt1n_trans_general with (twsucc twwrong).
      * apply succ_w_inner_reduces. apply IHHmap.
        split. apply succ_inner_normal_form. assumption. assumption.
      * apply rt1n_step. apply EW_SuccWrong. apply BN_wrong.
  - destruct (value_dec t1).
    + inversion v; subst.
      * apply rt1n_step. apply EW_PredWrong.
        inversion H; subst; inversion Hmap; constructor.
      * exfalso. apply Hnorm. inversion H; subst; eexists; constructor; assumption.
    + apply rt1n_trans_general with (twpred twwrong).
      * apply pred_w_inner_reduces. apply IHHmap.
        split. apply pred_inner_normal_form. assumption. assumption.
      * apply rt1n_step. apply EW_PredWrong. apply BN_wrong.
  - destruct (value_dec t1).
    + inversion v; subst.
      * apply rt1n_step. apply EW_IszeroWrong.
        inversion H; subst; inversion Hmap; constructor.
      * exfalso. apply Hnorm. inversion H; eexists; constructor. assumption.
    + apply rt1n_trans_general with (twiszero twwrong).
      * apply iszero_w_inner_reduces. apply IHHmap.
        split; try (apply iszero_inner_normal_form); assumption.
      * apply rt1n_step. apply EW_IszeroWrong. apply BN_wrong.
  - destruct (value_dec t1).
    + inversion v; subst.
      * exfalso. apply Hnorm; inversion H.
        -- exists t2. apply E_IfTrue.
        -- exists t3. apply E_IfFalse.
      * apply rt1n_step. apply EW_IfWrong. apply BB_value_n.
        apply value_n_iff_value_n_w with t1. assumption. assumption.
    + apply rt1n_trans_general with (twifthenelse twwrong tw2 tw3).
      * apply ifthenelse_w_inner_reduces. apply IHHmap1; try assumption.
        split.
        -- intros [t' contra]. apply Hnorm.
           exists (tifthenelse t' t2 t3). apply E_If. assumption.
        -- assumption.
      * apply rt1n_step. apply EW_IfWrong. apply BB_w.
Qed.

Theorem stuck_implies_wrong : forall (t t' : term) (tw : term_w),
  term_mapping t tw -> t ==>* t' -> stuck t' -> tw ==>w* twwrong.
Proof.
  intros t t' tw Hmap Hstepst Hstuckt'.
  generalize dependent tw.
  induction Hstepst; intros.
  - apply stuck_implies_wrong_base with x; assumption.
  - destruct (term_mapping_forward y) as [yw Hmapyw].
    apply rt1n_trans with yw.
    + apply term_mapping_preserves_evalR with x y; assumption.
    + apply IHHstepst; assumption.
Qed.

Theorem wrong_implies_stuck : forall (t t' : term) (tw : term_w),
  term_mapping t tw -> t ==>* t' -> normal_form t' -> tw ==>w* twwrong -> stuck t'.
Proof.
  intros t t' tw Hmap Hstepst Hnormt' Hstepstw.
  generalize dependent tw.
  induction Hstepst; intros.
  - inversion Hmap; subst; try (by (inversion Hstepstw; subst; inversion H)).
    + split. assumption. intros contra. inversion contra; subst; inversion H0; subst.
      inversion Hstepstw; subst.
      apply value_n_w_is_normal_form_w with (twsucc tw1).
      * apply value_n_iff_value_n_w with (tsucc t1); assumption.
      * exists y. assumption.
    + split. assumption. intros contra. inversion contra; subst; inversion H0; subst.
    + split. assumption. intros contra. inversion contra; subst; inversion H0; subst.
    + split. assumption. intros contra. inversion contra; subst; inversion H2.
  - destruct (term_mapping_forward y) as [yw Hmapyw].
    inversion Hstepstw; subst.
    + inversion Hmap.
    + assert (Heq : yw = y0).
      { apply term_mapping_forward_unique with y. assumption.
        apply evalR_preserves_mapping with x tw; assumption.
      }
      subst.
      apply IHHstepst with y0; assumption.
Qed.

Lemma ex_3_5_16 : forall (t t' : term) (tw : term_w),
  term_mapping t tw -> t ==>* t' -> normal_form t' ->
  stuck t' <-> tw ==>w* twwrong.
Proof.
  intros t t' tw Hmap Hstepst Hnormt'. split.
  - apply stuck_implies_wrong with t; assumption.
  - apply wrong_implies_stuck with t; assumption.
Qed.

(* 3.5.17 *)

Reserved Notation "t '==v' v" (at level 90, left associativity).
Inductive big_stepR : relation term :=
  | B_Value : forall (t1 : term),
      value t1 -> t1 ==v t1
  | B_IfTrue : forall (t1 t2 t3 v2 : term),
      t1 ==v ttrue -> t2 ==v v2 -> tifthenelse t1 t2 t3 ==v v2
  | B_IfFalse : forall (t1 t2 t3 v3 : term),
      t1 ==v tfalse -> t3 ==v v3 -> tifthenelse t1 t2 t3 ==v v3
  | B_Succ : forall (t1 nv1 : term),
      value_n nv1 -> t1 ==v nv1 -> tsucc t1 ==v tsucc nv1
  | B_PredZ : forall (t1 : term),
      t1 ==v tZ -> tpred t1 ==v tZ
  | B_PredSucc : forall (t1 nv1 : term),
      value_n nv1 -> t1 ==v tsucc nv1 -> tpred t1 ==v nv1
  | B_IszeroZ : forall (t1 : term),
      t1 ==v tZ -> tiszero t1 ==v ttrue
  | B_IszeroSucc : forall (t1 nv1 : term),
      value_n nv1 -> t1 ==v tsucc nv1 -> tiszero t1 ==v tfalse
  where "t '==v' v" := (big_stepR t v) : type_scope.

Lemma succ_outer_big_step : forall (t v : term),
  tsucc t ==v tsucc v -> t ==v v.
Proof.
  intros t v Hbig.
  inversion Hbig; subst.
  - apply B_Value. apply V_nat.
    inversion H1; subst; inversion H; subst. assumption.
  - assumption.
Qed.

Lemma evalR_step_same_big_stepR : forall (t t' v : term),
  value v -> t ==> t' -> t' ==v v -> t ==v v.
Proof.
  intros t t' v Hval Hstept Hbigt'.
  generalize dependent v.
  induction Hstept; intros v Hval Hbigt'.
  - apply B_IfTrue. apply B_Value. apply V_bool. apply V_true. assumption.
  - apply B_IfFalse. apply B_Value. apply V_bool. apply V_false. assumption.
  - inversion Hbigt'; subst.
    + inversion Hval; inversion H0.
    + apply B_IfTrue.
      * apply IHHstept. apply V_bool. apply V_true. assumption.
      * assumption.
    + apply B_IfFalse.
      * apply IHHstept. apply V_bool. apply V_false. assumption.
      * assumption.
  - inversion Hbigt'; subst.
    + apply B_Succ.
      * inversion Hval; inversion H0. assumption.
      * apply IHHstept;
        try (apply B_Value); inversion Hval; inversion H0; apply V_nat; assumption.
    + apply B_Succ. assumption.
      apply IHHstept.
      * inversion H0; apply V_nat. constructor. constructor. assumption.
      * assumption.
  - inversion Hbigt'. apply B_PredZ. apply B_Value. apply V_nat. apply V_Z.
  - apply B_PredSucc.
    + inversion Hval; subst.
      * inversion H; subst.
        -- inversion Hbigt'. apply V_Z.
        -- inversion Hbigt'; subst; apply V_succ; assumption.
      * assumption.
    + apply B_Succ.
      * inversion H; subst.
        -- inversion Hbigt'. apply V_Z.
        -- inversion Hbigt'; subst; apply V_succ; assumption.
      * assumption.
  - inversion Hbigt'; subst.
    + inversion Hval; inversion H0.
    + apply B_PredZ. apply IHHstept; assumption.
    + inversion H0; subst.
      * apply B_PredSucc. assumption.
        apply IHHstept.
        -- apply V_nat. apply V_succ. apply V_Z.
        -- assumption.
      * apply B_PredSucc.
        -- apply V_succ. assumption.
        -- apply IHHstept. apply V_nat. apply V_succ. assumption.
           assumption.
  - inversion Hbigt'. apply B_IszeroZ. apply B_Value. apply V_nat. apply V_Z.
  - inversion Hbigt'. apply B_IszeroSucc with t1. assumption.
    apply B_Succ. assumption.
    apply B_Value. apply V_nat. assumption.
  - inversion Hbigt'; subst.
    + inversion Hval; inversion H0.
    + apply B_IszeroZ. apply IHHstept.
      * apply V_nat. apply V_Z.
      * assumption.
    + apply B_IszeroSucc with nv1. assumption.
      apply IHHstept. apply V_nat. apply V_succ. assumption.
      assumption.
Qed.

Theorem evalR_implies_big_stepR : forall (t v : term),
  value v -> t ==>* v -> t ==v v.
Proof.
  intros t v Hval Hsteps.
  induction Hsteps.
  - inversion Hval; subst.
    + inversion H; subst; apply B_Value; assumption.
    + inversion H; subst.
      * apply B_Value. assumption.
      * apply B_Value. apply V_nat. apply V_succ. assumption.
  - apply evalR_step_same_big_stepR with y; try assumption.
    apply IHHsteps. assumption.
Qed.

Theorem big_stepR_implies_evalR : forall (t v : term),
  value v -> t ==v v -> t ==>* v.
Proof.
  intros t v Hval Hbig.
  induction Hbig.
  - apply rt1n_refl.
  - apply rt1n_trans_general with (tifthenelse ttrue t2 t3).
    + apply ifthenelse_inner_reduces. apply IHHbig1. apply V_bool. apply V_true.
    + apply rt1n_trans with t2.
      * apply E_IfTrue.
      * apply IHHbig2. assumption.
  - apply rt1n_trans_general with (tifthenelse tfalse t2 t3).
    + apply ifthenelse_inner_reduces. apply IHHbig1. apply V_bool. apply V_false.
    + apply rt1n_trans with t3.
      * apply E_IfFalse.
      * apply IHHbig2. assumption.
  - apply succ_inner_reduces. apply IHHbig. apply V_nat. assumption.
  - apply rt1n_trans_general with (tpred tZ).
    + apply pred_inner_reduces. apply IHHbig. assumption.
    + apply rt1n_step. apply E_PredZ.
  - apply rt1n_trans_general with (tpred (tsucc nv1)).
    + apply pred_inner_reduces. apply IHHbig. apply V_nat. apply V_succ. assumption.
    + apply rt1n_step. apply E_PredSucc. assumption.
  - apply rt1n_trans_general with (tiszero tZ).
    + apply iszero_inner_reduces. apply IHHbig. apply V_nat. apply V_Z.
    + apply rt1n_step. apply E_IszeroZ.
  - apply rt1n_trans_general with (tiszero (tsucc nv1)).
    + apply iszero_inner_reduces. apply IHHbig. apply V_nat. apply V_succ. assumption.
    + apply rt1n_step. apply E_IszeroSucc. assumption.
Qed.

Lemma ex_3_5_17 : forall (t v : term),
  value v ->
  t ==>* v <-> t ==v v.
Proof.
  intros t v Hval. split.
  - apply evalR_implies_big_stepR. assumption.
  - apply big_stepR_implies_evalR. assumption.
Qed.
