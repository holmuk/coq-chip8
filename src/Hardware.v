From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Integers.
Require Import Coqlib.
Require Import Maps.

Import Int.

(** Hardware specification *)

(** In general, coq-chip8 and original CHIP-8 has much in common if we speak about general approaches to ISA design.
  The big difference is that coq-chip8 has no keyboard nor display at all, it's better to consider our implementation as an abstract machine that realizes
  a subset of CHIP-8 ISA.
*)

(**
  coq-chip8 has 16 general purpose registers (V0 - VF) and three special ones (SP: Stack Pointer, PC: Program Counter and AReg: Address Register).
  We use AReg to work with memory. In original CHIP-8 we use the I register.
  *)

Inductive VReg : Type :=
  | v0: VReg | v1: VReg | v2: VReg | v3: VReg
  | v4: VReg | v5: VReg | v6: VReg | v7: VReg
  | v8: VReg | v9: VReg | vA: VReg | vB: VReg
  | vC: VReg | vD: VReg | vE: VReg | vF: VReg.

Inductive Reg : Type :=
  | VR: VReg -> Reg
  | PC: Reg
  | SP: Reg
  | AReg: Reg.

Coercion VR: VReg >-> Reg.

Lemma Reg_eq: forall (x y: Reg), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Module RegEq.
  Definition t := Reg.
  Definition eq := Reg_eq.
End RegEq.

Module RegMap := EMap (RegEq).

Definition RegFile := RegMap.t int.

(**
  In our implementation memory is an almost unbound set of words.
  *)

Module IntEq.
  Definition t := int.
  Definition eq := Int.eq_dec.
End IntEq.

Module MemoryMap := EMap (IntEq).

Definition Memory := MemoryMap.t int.

Definition EmptyMemory :=
  MemoryMap.init (repr 0%Z).

(**
  I decided to separate the stack from the main memory to not check bounds of the stack
  *)

Definition Stack := list int.

(**
  The instructions of coq-chip8 are the same as the instructions of original CHIP-8 ISA, with some exceptions:
  1) No instructions related with keyboard/display are realized
  2) cls clears the memory, not a part of
  3) ldr and str work only with individual registers
*)

Inductive Instruction : Type :=
  | Icls: Instruction
  | Irts: Instruction
  | Ijmp: int -> Instruction
  | Ijsr: int -> Instruction
  | Iskeqb: VReg -> int -> Instruction (* skeq for byte *)
  | Iskneb: VReg -> int -> Instruction (* skne for byte *)
  | Iskeqr: VReg -> VReg -> Instruction (* skeq for VReg *)
  | Iskner: VReg -> VReg -> Instruction (* skne for VReg *)
  | Imovr: VReg -> VReg -> Instruction (* mov for VReg *)
  | Imovb: VReg -> int -> Instruction (* mov for byte *)
  | Ior: VReg -> VReg -> Instruction
  | Iand: VReg -> VReg -> Instruction
  | Ixor: VReg -> VReg -> Instruction
  | Iadd: VReg -> VReg -> Instruction
  | Isub: VReg -> VReg -> Instruction
  | Irsb: VReg -> VReg -> Instruction
  | Ishr: VReg -> Instruction
  | Ishl: VReg -> Instruction
  | Imvi: int -> Instruction
  | Istr: VReg -> Instruction
  | Ildr: VReg -> Instruction
  | Inop: Instruction.

Definition code := list Instruction.

Module InstructionMap := MemoryMap.

Definition InstructionMemory := MemoryMap.t Instruction.

Definition EmptyInstructionMemory :=
  MemoryMap.init (Inop).

(** * Operational semantics of coq-chip8 *)

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (RegMap.set b c a) (at level 1, b at next level).

Fixpoint LoadCodeTo (c: code) (IM: InstructionMemory) (pc: int) : InstructionMemory :=
  match c with
  | nil => IM
  | h::t => LoadCodeTo t (InstructionMap.set pc h IM) (add pc (repr 2%Z))
  end.

Definition LoadCode (c: code) (IM: InstructionMemory) : InstructionMemory :=
  LoadCodeTo c IM (repr 0%Z).

Import ListNotations.

Definition NextPC RF :=
  (add (RF#PC) (repr 2%Z)).

(** Output is either a triple or Fail *)

Inductive Output: Type :=
  | Fine: Memory -> InstructionMemory -> RegFile -> Stack -> Output
  | Fail: Output.

Definition Skip M IM RF St cond : Output :=
   if cond then
      Fine M IM (RF#PC <- (add (NextPC RF) (repr 2%Z))) St
    else
      Fine M IM (RF#PC <- (NextPC RF)) St.

Definition ExecuteStep (M: Memory) IM RF St : Output :=
  let instr := IM RF#PC in
  match instr with
  | Icls =>
    Fine EmptyMemory IM (RF#PC <- (NextPC RF)) St
  | Irts =>
    match St with
    | [] => Fail
    | h::t =>
      Fine M IM (RF#PC <- h) t
    end
  | Ijmp i =>
    Fine M IM (RF#PC <- i) St
  | Ijsr i =>
    Fine M IM (RF#PC <- i) ((RF#PC)::St)
  | Iskeqb v b =>
    Skip M IM RF St (eq RF#v b)
  | Iskeqr v v' =>
    Skip M IM RF St (eq RF#v RF#v')
  | Iskneb v b =>
    Skip M IM RF St (negb (eq RF#v b))
  | Iskner v v' =>
    Skip M IM RF St (negb (eq RF#v RF#v'))
  | Imovb v b =>
    Fine M IM ((RF#v <- b)#PC <- (NextPC RF)) St
  | Imovr v v' =>
    Fine M IM ((RF#v <- (RF#v'))#PC <- (NextPC RF)) St
  | Ior v v' =>
    Fine M IM ((RF#v <- (or (RF#v) (RF#v')))#PC <- (NextPC RF)) St
  | Ixor v v' =>
    Fine M IM ((RF#v <- (xor (RF#v) (RF#v')))#PC <- (NextPC RF)) St
  | Iand v v' =>
    Fine M IM ((RF#v <- (and (RF#v) (RF#v')))#PC <- (NextPC RF)) St
  | Iadd v v' =>
    Fine M IM (((RF#v <- (add (RF#v) (RF#v')))#vF <- (add_carry (RF#v) (RF#v') (zero)))#PC <- (NextPC RF)) St
  | Isub v v' =>
    Fine M IM (((RF#v <- (sub (RF#v) (RF#v')))#vF <- (sub_borrow (RF#v) (RF#v') (zero)))#PC <- (NextPC RF)) St
  | Irsb v' v =>
    Fine M IM (((RF#v <- (sub (RF#v) (RF#v')))#vF <- (sub_borrow (RF#v) (RF#v') (zero)))#PC <- (NextPC RF)) St
  | Ishr v =>
    let cr := (shr RF#v one) in
    if (eq (mul cr (repr 2%Z)) RF#v) then
      Fine M IM (((RF#v <- cr)#vF <- zero)#PC <- (NextPC RF)) St
    else
      Fine M IM (((RF#v <- cr)#vF <- one)#PC <- (NextPC RF)) St
  | Ishl v =>
    Fine M IM (((RF#v <- (shl RF#v one))#vF <- (and RF#v one))#PC <- (NextPC RF)) St
  | Imvi i =>
    Fine M IM ((RF#AReg <- i)#PC <- (NextPC RF)) St
  | Istr v =>
    Fine (MemoryMap.set (RF#v) (RF#AReg) M) IM (RF#PC <- (NextPC RF)) St
  | Ildr v =>
    Fine M IM ((RF#v <- (M (RF#AReg)))#PC <- (NextPC RF)) St
  | Inop =>
    Fine M IM RF St
  end.

(** It's not the truth every program will end up within finite time, so I decided to introduce n *)

Fixpoint ExecuteNSteps (M: Memory) IM RF St (n: nat) : Output :=
  match n with
  | 0%nat => Fine M IM RF St
  | (S n')%nat =>
    let Ex := ExecuteStep M IM RF St in
    match Ex with
    | Fine M' IM' RF' St' =>
      ExecuteNSteps M' IM' RF' St' n'
    | Fail => Fail
    end
  end.

(** Automatisation to reason about coq-chip8 programs *)

Definition Run C n : Output :=
  ExecuteNSteps EmptyMemory
    (LoadCode C EmptyInstructionMemory)
    (RegMap.init zero) [] n.

Hint Unfold LoadCode EmptyInstructionMemory EmptyMemory : chipmem.
Hint Unfold ExecuteNSteps ExecuteStep NextPC Skip Run : chipmem.
Hint Unfold MemoryMap.init InstructionMap.init MemoryMap.set InstructionMap.set : chipmem.
Hint Unfold RegMap.init RegMap.set IntEq.eq RegEq.eq zero : chipmem.

Lemma Z_eq_eq: forall x,
  eq (repr x) (repr x) = true.
Proof.
  intros. unfold eq. unfold zeq. rewrite unsigned_repr_eq.
  case (Z.eq_dec _ _); intros; intuition.
Qed.

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
(*
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
*)
Ltac inverse_eq :=
  match goal with
  | H: ?x = ?y |- _ => try inversion H
  end.

Hint Unfold eq zeq : Z_unfold.

Lemma Z_eq_neq:
  eq (repr 4) (repr 5) = false.
Proof.
  unfold eq. unfold zeq.
  case (Z.eq_dec _ _); intros; intuition.
  inverse_eq.
Qed.
(*
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
  end.*)

Definition OutputM (Out: Output) : option Memory :=
  match Out with
  | Fail => None
  | Fine M _ _ _ => Some M
  end.

Definition OutputIM (Out: Output) : option InstructionMemory :=
  match Out with
  | Fail => None
  | Fine _ IM _ _ => Some IM
  end.

Definition OutputRF (Out: Output) : option RegFile :=
  match Out with
  | Fail => None
  | Fine _ _ RF _ => Some RF
  end.

Definition OutputStack (Out: Output) : option Stack :=
  match Out with
  | Fail => None
  | Fine _ _ _ St => Some St
  end.

Hint Unfold OutputM OutputIM OutputRF OutputStack : chipmem.
