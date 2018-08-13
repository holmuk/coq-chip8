Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Import Int.
Require Import Hardware.

Ltac dec_eq_try :=
  repeat (rewrite dec_eq_false;
    [ idtac | solve [ let F := fresh in (intro F; inversion F)] ] +
  rewrite dec_eq_true + fail).

Ltac simpl_code :=
  repeat autounfold with chipmem; simpl;
  repeat match goal with
  | |- context[add (repr ?x) (repr ?y)] =>
    let GR := fresh in assert (GR: add (repr x) (repr y) = repr (x + y)) by
      (rewrite add_unsigned; rewrite unsigned_repr_eq; rewrite <- Z_mod_modulus_eq;
      apply f_equal; auto); rewrite GR; clear GR; simpl
  | |- context[?x # ?y <- ?z] =>
    change (x # y <- z) with (RegMap.set y z x); try unfold RegMap.set
  end; repeat autounfold with chipmem; simpl.

Ltac deal_with_eq_dec :=
  repeat (let F := fresh in
   (case (eq_dec _ _); intro F; try inversion F));
  repeat match goal with
  | |- context[Reg_eq ?x ?x] =>
    rewrite dec_eq_true
  | H: context[Reg_eq ?x ?x] |- _ =>
    rewrite dec_eq_true in H; try rewrite H
  end; repeat (case (Reg_eq _ _); intros).

Ltac inverse_eq :=
  match goal with
  | H: ?x = ?y |- _ => try inversion H
  end.

Ltac deal_with_eq :=
  repeat match goal with
  | |- context [eq ?x ?x] =>
    rewrite Z_eq_eq
  | H: context[eq ?x ?x] |- _ =>
    rewrite Z_eq_eq in H
  end; autounfold with Z_unfold;
  try (case (Z.eq_dec _ _); intros; [intuition | inverse_eq]); simpl in *.

Ltac Fine_eq :=
  match goal with
  | |- context[Fine ?M' ?IM' ?RF' ?St' = Fine _ _ _ _ /\ _] =>
    exists M'; exists IM'; exists RF'; exists St'
  end.

Lemma rsb_is_reverse_sub: forall M IM RF St v v',
  (IM (RF#PC)) = (Isub v v') ->
  let EIMsub := ExecuteStep M IM RF St in
  let EIMrsb := ExecuteStep M (InstructionMap.set (RF#PC) (Irsb v' v) IM) RF St in
  OutputM EIMsub = OutputM EIMrsb /\
  OutputRF EIMsub = OutputRF EIMrsb /\
  OutputStack EIMsub = OutputStack EIMrsb.
Proof.
  intros. subst EIMsub. subst EIMrsb.
  simpl_code. rewrite H. simpl.
  dec_eq_try. destruct (lt _ _); auto.
Qed.
