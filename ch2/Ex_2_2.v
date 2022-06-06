From Coq Require Import Relations.Relation_Definitions.

Inductive rc {S : Type} (R : relation S) : relation S :=
  | rc_incl : forall r1 r2 : S, R r1 r2 -> rc R r1 r2
  | rc_refl : forall s : S, rc R s s.

Definition reflexive_closure {S : Type} (R U : relation S) : Prop :=
  reflexive S U /\
  inclusion S R U /\
  (forall (T : relation S), reflexive S T -> inclusion S R T -> inclusion S U T).

Lemma ex_2_2_6 : forall (S :  Type) (R : relation S),
  reflexive_closure R (rc R).
Proof.
  repeat split.
  - unfold reflexive. intros. apply rc_refl.
  - unfold inclusion. intros. apply rc_incl. apply H.
  - intros T reflT inclT.
    unfold inclusion. intros.
    inversion H; subst; auto.
Qed.

Inductive tc {S : Type} (R : relation S) : relation S :=
  | tc_incl : forall r1 r2 : S, R r1 r2 -> tc R r1 r2
  | tc_trans : forall (s t u : S), tc R s t -> tc R t u -> tc R s u.

Definition transitive_closure {S : Type} (R U : relation S) : Prop :=
  transitive S U /\
  inclusion S R U /\
  (forall (T : relation S), transitive S T -> inclusion S R T -> inclusion S U T).

Lemma ex_2_2_7 : forall (S : Type) (R : relation S),
  transitive_closure R (tc R).
Proof.
  repeat split.
  - unfold transitive. intros. apply tc_trans with y; assumption.
  - unfold inclusion. intros. apply tc_incl. apply H.
  - intros T transT inclT.
    unfold inclusion. intros.
    induction H.
    + apply inclT. apply H.
    + apply transT with t; assumption.
Qed.

Inductive rtc {S : Type} (R : relation S) : relation S :=
  | rtc_incl : forall r1 r2 : S, R r1 r2 -> rtc R r1 r2
  | rtc_refl : forall s : S, rtc R s s
  | rtc_trans : forall s t u : S, rtc R s t -> rtc R t u -> rtc R s u.

Definition reflexive_transitive_closure {S : Type} (R U : relation S) : Prop :=
  reflexive S U /\
  transitive S U /\
  inclusion S R U /\
  (forall (T : relation S), 
    reflexive S T -> transitive S T -> inclusion S R T -> inclusion S U T).

Lemma rtc_valid : forall (S : Type) (R : relation S), 
  reflexive_transitive_closure R (rtc R).
Proof.
  repeat split.
  - unfold reflexive. intros. apply rtc_refl.
  - unfold transitive. intros. apply rtc_trans with y; assumption.
  - unfold inclusion. intros. apply rtc_incl. assumption.
  - intros T H_Trefl H_Ttrans H_Tincl.
    unfold inclusion. intros.
    induction H.
    + apply H_Tincl. assumption.
    + apply H_Trefl.
    + apply H_Ttrans with t; assumption.
Qed.

Definition predicate (S : Type) : Type := S -> Prop.

Definition preserved_by (S : Type) (P : predicate S) (R : relation S) : Prop :=
  forall (s s' : S), R s s' -> P s -> P s'.

Lemma ex_2_2_8 : forall (S : Type) (R : relation S) (P : predicate S),
  preserved_by S P R -> preserved_by S P (rtc R).
Proof.
  intros S R P H_R_preserves_P.
  unfold preserved_by.
  intros s s' H_rtcRss' H_Ps.
  induction H_rtcRss'; subst.
  - apply (H_R_preserves_P r1 r2); assumption.
  - assumption.
  - apply IHH_rtcRss'2. apply IHH_rtcRss'1. assumption.
Qed.
