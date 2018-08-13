Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.
Require Import ChipTactics.

Import ListNotations.
Import Int.

Definition SimpleSkipper :=
  [(Imovb v0 (Int.repr 4));
   (Iskeqb v0 (Int.repr 4));
   (Imovb v0 (Int.repr 8));
   (Icls)].

Lemma SimpleSkipper_is_ok:
  exists n M IM RF St,
  Run SimpleSkipper n = Fine M IM RF St /\
  RF#v0 = (repr 4).
Proof.
  exists 3%nat. unfold SimpleSkipper. simpl_code. dec_eq_try.
  deal_with_eq. dec_eq_try.
  Fine_eq. intuition. dec_eq_try.
  reflexivity.
Qed.