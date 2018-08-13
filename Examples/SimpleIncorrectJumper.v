Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.
Require Import ChipTactics.

Import ListNotations.
Import Int.

Definition SimpleJumperNotOk :=
  [(Irts)].

Definition NotCorrect C :=
  exists n, Run C n = Fail.

Lemma SimpleJumperNotOk_not_ok:
  NotCorrect SimpleJumperNotOk.
Proof.
  unfold NotCorrect.
  exists 5%nat. unfold SimpleJumperNotOk.
  simpl_code. dec_eq_try; auto.
Qed.