Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.

Import ListNotations.
Import Int.

(** Find a maximum of v0 and v1 and load it to v2 *)

Definition ChipMax (a b: int) :=
  [(Imovb v0 a);
   (Imovb v1 b);
   (Imovr v3 v0);
   (Isub v3 v1);
   (Iskeqb vF zero);
   (Imovr v2 v1);
   (Iskneb vF zero);
   (Imovr v2 v0);
   (Imovb vF zero)].

Lemma lt_eq: forall x,
  lt (repr x) (repr x) = false.
Proof.
  unfold lt. intros. rewrite signed_repr_eq.
  apply zlt_false. destruct (zlt _ _); intuition.
Qed.

Lemma lt_pos_true: forall x y,
  x < y -> 0 <= x < half_modulus -> 0 <= y < half_modulus ->
  lt (repr x) (repr y) = true.
Proof.
  intros. unfold lt. repeat rewrite signed_repr_eq.
  rewrite half_modulus_modulus.
  apply zlt_true.
  repeat rewrite Zmod_small; intuition.
  repeat rewrite zlt_true; intuition.
Qed.

Lemma lt_pos_false: forall x y,
  y <= x -> 0 <= x < half_modulus -> 0 <= y < half_modulus ->
  lt (repr x) (repr y) = false.
Proof.
  intros. unfold lt. repeat rewrite signed_repr_eq.
  rewrite half_modulus_modulus.
  apply zlt_false.
  repeat rewrite Zmod_small; intuition.
  repeat rewrite zlt_true; intuition.
Qed.

Ltac dec_eq_try :=
  repeat (rewrite dec_eq_false;
    [ idtac | solve [ let F := fresh in (intro F; inversion F)] ] +
  rewrite dec_eq_true + fail).

Lemma ChipMax_ex_ok:
  exists n M IM RF St,
  Run (ChipMax (repr 3) (repr 5)) n = Fine M IM RF St /\
  RF#v2 = (repr 5).
Proof.
  exists 9%nat. unfold ChipMax. simpl_code.

  dec_eq_try.

  rewrite lt_pos_true. dec_eq_try.
  deal_with_eq. simpl_code. dec_eq_try.

  rewrite pred_dec_false; [ idtac | dec_eq_try].
  simpl.
  dec_eq_try.
  Fine_eq; intuition. simpl_code.
  dec_eq_try.
  all: intuition.
  - inversion H.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.

Lemma ChipMax_ok: forall a b,
  0 <= a < half_modulus ->
  0 <= b < half_modulus ->
  exists n M IM RF St,
    Run (ChipMax (repr a) (repr b)) n = Fine M IM RF St /\
  RF#v2 = repr (Z.max a b).
Proof.
  intros.
  exists 9%nat. unfold ChipMax. simpl_code.
  dec_eq_try.
  destruct (zlt a b).
  - rewrite lt_pos_true; auto. dec_eq_try.
  deal_with_eq. simpl_code. dec_eq_try.
  rewrite pred_dec_false; [ idtac | dec_eq_try].
  simpl.
  dec_eq_try.
  Fine_eq; intuition. simpl_code.
  dec_eq_try.
  + rewrite Zmax_spec. destruct (zlt _ _). intuition. auto.
  + intro. inversion H1.
  - rewrite lt_pos_false; auto. dec_eq_try.
  deal_with_eq. simpl_code. dec_eq_try.
  rewrite pred_dec_true; [ idtac | dec_eq_try].
  simpl.
  dec_eq_try.
  Fine_eq; intuition. simpl_code.
  dec_eq_try.
  + rewrite Zmax_left; auto.
  + auto.
  + intuition.
Qed.