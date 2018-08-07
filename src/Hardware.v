From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import chip8.Integers.
Require Import chip8.Coqlib.
Require Import chip8.Maps.

Import Int.

(** *
  CHIP-8 has 16 8-bit data registers (V0-VF) and one special 16-bit address register.
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

Notation "'I'" := AReg (only parsing).

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

(** *
  Memory is simple in Chip-8.
  I think it's possible not to use Memory.v from CopmCert.
  *)

Module ByteEq.
  Definition t := int.
  Definition eq := Int.eq_dec.
End ByteEq.

Module MemoryMap := EMap (ByteEq).
Definition Memory := MemoryMap.t int.

(**
  Stack is just a list of addresses.
  *)


Definition Stack := list int.

(**
  Instructions of Chip-8
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
  | Ishr: VReg -> Instruction
  | Ishl: VReg -> Instruction
  | Irsb: VReg -> VReg -> Instruction
  | Imvi: int -> Instruction
  | Ijmi: int -> Instruction
  | Iadi: VReg -> Instruction
  | Istr: VReg -> Instruction
  | Ildr: VReg -> Instruction.

Definition code := list Instruction.

Module IntEq.
  Definition t := int.
  Definition eq := Int.eq_dec.
End IntEq.

Module InstructionMap := EMap (IntEq).

Definition InstructionMemory := InstructionMap.t Instruction.

(** Code is stored in InstructionMemory *)

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

Definition EmptyInstructionMemory :=
  InstructionMap.init (Icls).

Definition EmptyMemory :=
  MemoryMap.init (repr 0%Z).

Definition NextPC RF :=
  (add (RF#PC) (repr 2%Z)).

(** Output is either a triple or Fail *)

Inductive Output: Type :=
  | Fine: Memory -> InstructionMemory -> RegFile -> Stack -> Output
  | Fail: Output.

Definition StackArea :=
  (repr 96%Z).

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
    Fine M IM ((RF#v <- (add (RF#v) (RF#v')))#PC <- (NextPC RF)) St
  | Isub v v' =>
    if (lt RF#v RF#v') then
      Fine M IM (((RF#v <- (sub (RF#v) (RF#v'))#vF <- one))#PC <- (NextPC RF)) St
    else
      Fine M IM ((RF#v <- (sub (RF#v) (RF#v')))#PC <- (NextPC RF)) St
  | Irsb v' v =>
    if (lt RF#v RF#v') then
      Fine M IM (((RF#v <- (sub (RF#v) (RF#v'))#vF <- one))#PC <- (NextPC RF)) St
    else
      Fine M IM ((RF#v <- (sub (RF#v) (RF#v')))#PC <- (NextPC RF)) St
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
  | Ijmi i =>
    Fine M IM (RF#PC <- (add i RF#v0)) St
  | Iadi v =>
    Fine M IM ((RF#AReg <- (add (RF#v) (RF#AReg)))#PC <- (NextPC RF)) St
  | Istr v =>
    Fine (MemoryMap.set (RF#v) (RF#AReg) M) IM (RF#PC <- (NextPC RF)) St
  | _ => Fail
  end.

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

Definition SampleCode :=
  [(Imovb v0 (Int.repr 4%Z));
   (Imovb v1 (Int.repr 5%Z));
   (Iadd v0 v1)].

Hint Unfold LoadCode SampleCode EmptyInstructionMemory EmptyMemory : chipmem.
Hint Unfold ExecuteNSteps ExecuteStep NextPC : chipmem.
Hint Unfold MemoryMap.init InstructionMap.init MemoryMap.set InstructionMap.set : chipmem.
Hint Unfold RegMap.init RegMap.set IntEq.eq RegEq.eq zero : chipmem.

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

Ltac deal_with_eq :=
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

Lemma SampleCode_is_fine:
  exists n M IM RF St,
  ExecuteNSteps EmptyMemory
    (LoadCode SampleCode EmptyInstructionMemory)
    (RegMap.init zero) [] n = Fine M IM RF St /\
  RF#v0 = (repr 9%Z).
Proof.
  exists 3%nat.
  simpl_code. deal_with_eq.
  all: match goal with
  | |- context[Fine ?M' ?IM' ?RF' ?St' = Fine _ _ _ _ /\ _] =>
    exists M'; exists IM'; exists RF'; exists St'
  end.
  all: try inverse_eq.
  all: intuition. deal_with_eq; try inverse_eq.
  intuition.
Qed.
