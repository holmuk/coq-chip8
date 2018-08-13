Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.
Require Import ChipTactics.

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
  + rewrite Zmax_right; auto. apply Z.lt_le_incl; assumption.
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

Lemma ChipMax_ex_ok:
  exists n M IM RF St,
  Run (ChipMax (repr 3) (repr 5)) n = Fine M IM RF St /\
  RF#v2 = (repr 5).
Proof.
  apply ChipMax_ok.
  all: rewrite half_modulus_power; simpl; unfold two_power_pos; simpl; intuition.
Qed.