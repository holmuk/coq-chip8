Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.
Require Import ChipTactics.

Import ListNotations.
Import Int.

Definition SimpleAddition :=
  [(Imovb v0 (Int.repr 4%Z));
   (Imovb v1 (Int.repr 5%Z));
   (Iadd v0 v1)].

Lemma SimpleAddition_is_ok:
  exists n M IM RF St,
  Run SimpleAddition n = Fine M IM RF St /\
  RF#v0 = (repr 9%Z).
Proof.
  exists 3%nat. unfold SimpleAddition.
  simpl_code. dec_eq_try.
  Fine_eq. intuition. dec_eq_try.
  simpl_code. reflexivity.
Qed.