Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Require Import Hardware.

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
  simpl_code. deal_with_eq_dec; auto.
  contradiction.
Qed.