Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.

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
  exists 3%nat. unfold SimpleSkipper. simpl_code. deal_with_eq_dec.
  all: try Fine_eq; try inverse_eq; deal_with_eq_dec.
  all: deal_with_eq; deal_with_eq_dec; try Fine_eq.
  all: intuition.
  deal_with_eq_dec. inverse_eq. auto.
Qed.