From compcert.x86 Require Asm.
From compcert.common Require Import AST Memory.
From compcert.lib Require Import Integers.
Require Import ZArith.
Definition ireg := Asm.ireg.

Definition int := compcert.lib.Integers.int.
Definition int64 := compcert.lib.Integers.int64.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

  The body of the instruction' type was taken from the CompCert project's 
  x86/Asm.v.  The instructions we support have been moved to the top, 
  preserving the order of the commented out instructions.

  Naming conventions for types:
  - [b]: 8 bits
  - [w]: 16 bits ("word")
  - [l]: 32 bits ("longword")
  - [q]: 64 bits ("quadword")
  - [d] or [sd]: FP double precision (64 bits)
  - [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
  - [r]: integer register operand
  - [f]: XMM register operand
  - [m]: memory operand
  - [i]: immediate integer operand
  - [s]: immediate symbol operand
  - [l]: immediate label operand
  - [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.

 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
Inductive instruction': Type :=
  | Pmov_rr' (rd: ireg) (r1: ireg)       (**r [mov] (integer) *)
  | Paddl_ri' (rd: ireg) (n: int)
  | Paddq_ri' (rd: ireg) (n: int64)
  | Pmovl_ri' (rd: ireg) (n: int)
  | Pmovq_ri' (rd: ireg) (n: int64)
  | Paddl_rr' (rd: ireg) (r2: ireg)

(*  
  (** Moves *)
  | Pmov_rs (rd: ireg) (id: ident)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
       *)
(*
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr (rd: ireg) (rs: ireg)     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr (rd: ireg)                (** 64 to 32 bit conversion (pseudo) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg) (**r double to signed long *)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)  (**r signed long to double *)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg) (**r single to signed long *)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)  (**r signed long to single *)
       *)
  (** Integer arithmetic *)
      (*| Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
       *)
      (*
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg)
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
       *)
  (** Floating-point arithmetic *)
      (*
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret
       *)
  (** Saving and restoring registers *)
      (*
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovq_rf (rd: ireg) (r1: freg)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Pnop
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64)
       *)
      .

Definition Pmov_rr := compcert.x86.Asm.Pmov_rr.
Definition Paddl_ri := compcert.x86.Asm.Paddl_ri.
Definition Paddq_ri := compcert.x86.Asm.Paddq_ri.
Definition Pmovl_ri := compcert.x86.Asm.Pmovl_ri.
Definition Pmovq_ri := compcert.x86.Asm.Pmovq_ri.
Definition Paddl_rr := compcert.x86.Asm.Paddl_rr.

Definition RAX := compcert.x86.Asm.RAX.
Definition RBX := compcert.x86.Asm.RBX.
Definition RCX := compcert.x86.Asm.RCX.
Definition RDX := compcert.x86.Asm.RDX.
Definition RSI := compcert.x86.Asm.RSI.
Definition RDI := compcert.x86.Asm.RDI.
Definition RBP := compcert.x86.Asm.RBP.
Definition RSP := compcert.x86.Asm.RSP.
Definition R8 := compcert.x86.Asm.R8.
Definition R9 := compcert.x86.Asm.R9.
Definition R10 := compcert.x86.Asm.R10.
Definition R11 := compcert.x86.Asm.R11.
Definition R12 := compcert.x86.Asm.R12.
Definition R13 := compcert.x86.Asm.R13.
Definition R14 := compcert.x86.Asm.R14.
Definition R15 := compcert.x86.Asm.R15.

Definition to_x86instruction (i:instruction') : Asm.instruction :=
  match i with
  | Pmov_rr' rd r1 => Pmov_rr rd r1
  | Paddl_ri' rd n => Paddl_ri rd n
  | Paddq_ri' rd n => Paddq_ri rd n
  | Pmovl_ri' rd n => Pmovl_ri rd n
  | Pmovq_ri' rd n => Pmovq_ri rd n
  | Paddl_rr' rd r2 => Paddl_rr rd r2
  end.


Definition code' := list instruction'.
Definition mkfunction := Asm.mkfunction.
Record function' : Type := mkfunction' { fn_sig: signature; fn_code: code' }.
Definition fundef' := AST.fundef function'.
Definition program' := AST.program fundef' unit.
Definition genv' := Globalenvs.Genv.t fundef' unit.
Definition regset := Asm.regset.

(* We need to embed genv' into CompCert's genv to wrap their exec_instr, which takes a genv argument.
   We start by embedding code', then function' and fundef', finally ending with genv'. 
*)

Definition to_code (c':code') :=
  List.map to_x86instruction c'.
Definition to_function (f':function') :=
  mkfunction (fn_sig f') (to_code (fn_code f')).
Definition to_fundef (fd':fundef') : Asm.fundef :=
  match fd' with
  | Internal func => Internal (to_function func)
  | External external_func => External external_func
  end.
Definition to_globdef (gb:globdef fundef' unit) :=
  match gb with
  | Gfun f' => Gfun (to_fundef f')
  | Gvar gv => Gvar gv
  end.

(*
Definition to_genv (g':genv') : Globalenvs.Genv.t Asm.fundef unit.
refine {|
    genv_public := (Globalenvs.Genv.genv_public g');
    genv_symb := (genv_symb g');
    genv_defs  := (Maps.PTree.map to_globdef (genv_defs g'));
    genv_next  := (genv_next g');
    genv_symb_range := (genv_symb_range g');
    genv_vars_inj := (genv_vars_inj g')
  |}.

Definition to_genv (g':genv') :=
  mkgenv 
    (genv_public g')
    (genv_symb g')
    (Maps.PTree.map to_globdef (genv_defs g'))
    (genv_next g')
    (genv_symb_range g')
    _TODO_
    (genv_vars_inj g')
    .
 *)



Definition outcome := Asm.outcome.
Definition function := Asm.function.
Definition mem := Memory.mem.

Definition exec_instr' (ge:Asm.genv) (f: function) (i: instruction') (rs: regset) (m: mem)  : outcome :=
  Asm.exec_instr ge f (to_x86instruction i) rs m.

Require Import List.
Import ListNotations.
Open Scope Z.



(* Start abstract insterpretation definition *)
From compcert.lib Require Import Maps.
From compcert.common Require Import Values.

Require Import Wlang Sign Abstract.

Module Type ConcreteISA (regs:EQUALITY_TYPE).
  Parameter instruction : Type.
  Module regmap := EMap(regs).
  Definition regset := regmap.t val.
  Parameter reglist : list regs.t.
  Parameter genv : Type.
  Definition code := list instruction.
  Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
  Definition fundef := AST.fundef function.
  Definition program := AST.program fundef unit.
  Parameter mem : Type.
  Parameter outcome : Type.

  (*Parameter exec_instr : genv -> function -> instruction -> regset -> mem -> outcome.*)
End ConcreteISA.

Module x86ISA <: ConcreteISA (Asm.PregEq).
  Definition instruction := instruction'.
  Module regmap := EMap(Asm.PregEq).
  Definition regset := regmap.t val.
  Definition genv := Asm.genv.
  Definition code := list instruction.
  Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
  Definition fundef := AST.fundef function.
  Definition program := AST.program fundef unit.
  Definition mem := Memory.mem.
  Definition outcome := Asm.outcome.

  Definition exec_instr := Asm.exec_instr.

  (* This reglist enumerates all hardware registers used for computing
     the equivalence of abstract and concrete states. *)
  Definition reglist := [Asm.PC; Asm.ST0; Asm.RA;
      Asm.IR Asm.RAX; Asm.IR Asm.RBX; Asm.IR Asm.RCX; Asm.IR Asm.RDX; Asm.IR Asm.RSI;
      Asm.IR Asm.RDI; Asm.IR Asm.RBP; Asm.IR Asm.RSP; Asm.IR Asm.R8; Asm.IR Asm.R9;
      Asm.IR Asm.R10; Asm.IR Asm.R11; Asm.IR Asm.R12; Asm.IR Asm.R13; Asm.IR Asm.R14;
      Asm.IR Asm.R15;
      Asm.FR Asm.XMM0; Asm.FR Asm.XMM1; Asm.FR Asm.XMM2; Asm.FR Asm.XMM3; Asm.FR Asm.XMM4;
      Asm.FR Asm.XMM5; Asm.FR Asm.XMM6; Asm.FR Asm.XMM7; Asm.FR Asm.XMM8; Asm.FR Asm.XMM9;
      Asm.FR Asm.XMM10; Asm.FR Asm.XMM11; Asm.FR Asm.XMM12; Asm.FR Asm.XMM13; Asm.FR Asm.XMM14;
      Asm.FR Asm.XMM15;
      Asm.CR Asm.ZF; Asm.CR Asm.CF; Asm.CR Asm.PF; Asm.CR Asm.SF; Asm.CR Asm.OF].
End x86ISA.


Module Type AbstractDomain.
  Parameter t : Type.
  Parameter top : t.
  Parameter eq : t -> t -> bool.
  Parameter join : t -> t -> t. (* least upper bound *)
  Parameter intersect : t -> t -> t. (* greatest lower bound *)
  (* Concretization function *)
  Parameter to_con : t -> (Values.val -> Prop).
  (* Abstraction function *)
  Parameter to_abs : Values.val -> t.
End AbstractDomain.

Inductive sign :=
  | SZero | SPos | STop | SBot.

Definition sign_eq : sign -> sign -> bool.
Proof.
  intros H H0. destruct H eqn:Eq1; destruct H0 eqn:Eq2.
  all: match goal with
      | [H: _ = ?x, H2: _ = ?x |- _] => exact true
      | |- _ => exact false
      end.
Defined.

(* least upper bound *)
Definition sign_join (s1 s2:sign) :=
  match s1, s2 with
  | SBot, x | x, SBot => x
  | STop, _ | _, STop => STop
  | SZero, SZero => SZero
  | SPos, SPos => SPos
  | SZero, SPos | SPos, SZero => STop
  end.

(* greatest lower bound *)
Definition sign_intersect (s1 s2:sign) :=
  match s1, s2 with
  | STop, x | x, STop => x
  | SBot, _ | _, SBot => SBot
  | SZero, SZero => SZero
  | SPos, SPos => SPos
  | SZero, SPos | SPos, SZero => SBot
  end.

Definition sign_to_con (s:sign) (v:Values.val) :=
  match s with 
  | SBot => False
  | STop => True
  | SZero => match v with
             | Vundef => False
             | Vint i => i = Int.zero
             | Vlong i64 => i64 = Int64.zero
             | Vfloat f => f = Floats.Float.zero
             | Vsingle s => s = Floats.Float32.zero 
             | Vptr b ofs =>  (Ptrofs.intval ofs) = 0
             end
  | SPos => match v with
            | Vundef => False
            | Vint i => Int.cmp Cgt i Int.zero = true
            | Vlong i64 => Int64.cmp Cgt i64 Int64.zero = true
            | Vfloat f => Floats.Float.cmp Cgt f  Floats.Float.zero = true
            | Vsingle s => Floats.Float32.cmp Cgt s Floats.Float32.zero = true
            | Vptr b ofs => (Ptrofs.intval ofs) > 0
            end
  end.

Definition sign_to_abs (v:Values.val) :=
  match v with
  | Vundef => SBot
  | Vint i => if Int.cmp Ceq i Int.zero then SZero else
              if Int.cmp Cgt i Int.zero then SPos else STop
  | Vlong i64 => if Int64.cmp Ceq i64 Int64.zero then SZero else
                 if Int64.cmp Cgt i64 Int64.zero then SPos else STop
  | Vfloat f => if Floats.Float.cmp Ceq f Floats.Float.zero then SZero else
                if Floats.Float.cmp Cgt f Floats.Float.zero then SPos else STop
  | Vsingle s => if Floats.Float32.cmp Ceq s Floats.Float32.zero then SZero else
                 if Floats.Float32.cmp Cgt s Floats.Float32.zero then SPos else STop
  | Vptr _ ofs => if Z.eqb (Ptrofs.intval ofs) 0 then SZero else
                  if Z.gtb (Ptrofs.intval ofs) 0 then SPos else STop
  end.


Module SignAbstractDomain <: AbstractDomain.
  Definition t := sign.
  Definition top := STop.
  Definition eq := sign_eq.
  Definition join := sign_join.
  Definition intersect := sign_intersect.
  Definition to_con := sign_to_con.
  Definition to_abs := sign_to_abs.
End SignAbstractDomain.

Module Type AbstractInterpreter (regs:EQUALITY_TYPE) (ISA: ConcreteISA regs) (Ab:AbstractDomain).
  Import Ab.
  Definition astate := ISA.regmap.t t.

  (* Abstract semantics of x86 instructions *)
  Parameter aexec_instr : ISA.instruction -> astate -> astate.
  Definition empty_astate := ISA.regmap.init top. 

  Definition get := @ISA.regmap.get Ab.t.
  Definition set := @ISA.regmap.set Ab.t.
  Definition state_eq (s1 s2 : astate) : bool :=
    let fix compare_keys ks := match ks with
                              | nil => true
                              | k :: ks' => let v1 := get k s1 in
                                            let v2 := get k s2 in
                              if Ab.eq v1 v2 then compare_keys ks' else false
                              end
    in compare_keys ISA.reglist.

  (* Join abstract state *) 
  Definition join_state (s1 s2 : astate) : astate :=
    let all_keys := ISA.reglist in
    let fix build_state keys :=
    match keys with
    | nil => empty_astate
    | k :: ks => let v1 := get k s1 in
                let v2 := get k s2 in
                let rest := build_state ks in
                set k (join v1 v2) rest
    end in
    build_state all_keys.


  (* Semantics of abstract instructions *) 
  Fixpoint abs_interp (c:ISA.code) (s:astate) : astate :=
    match c with
    | nil => s
    | i :: code' => abs_interp code' (aexec_instr i s)
    end.
End AbstractInterpreter.

Module x86SignAbstractInterpreter <: AbstractInterpreter (Asm.PregEq) (x86ISA) (SignAbstractDomain).
  Import SignAbstractDomain.
  (* Why are `set` and `get` from the AbstractInterpreter definition unavailable. *)
  Definition get := @x86ISA.regmap.get sign.
  Definition set := @x86ISA.regmap.set sign.

  Definition sign_of_int i := to_abs (Vint i).
  Definition sign_of_int64 i64 := to_abs (Vlong i64).
  Definition sign_add (s1 s2:sign) :=
    match s1, s2 with
    | SBot, _ | _, SBot => SBot
    | SZero, SZero => SZero
    | SPos, _ | _, SPos => SPos
    | STop, _ | _, STop => STop
    end.

  Definition aexec_instr i' s :=
    match i' with
    | Pmov_rr' iregd ireg2 => set (Asm.IR iregd) (s (Asm.IR ireg2)) s
    | Paddl_ri' iregd imm => set (Asm.IR iregd) (sign_add (s (Asm.IR iregd)) (sign_of_int imm)) s
    | Paddq_ri' iregd imm => set (Asm.IR iregd) (sign_add (s (Asm.IR iregd)) (sign_of_int64 imm)) s
    | Pmovl_ri' iregd imm  => set (Asm.IR iregd) (sign_of_int imm) s
    | Pmovq_ri' iregd imm => set (Asm.IR iregd) (sign_of_int64 imm) s
    | Paddl_rr' iregd ireg2 => set (Asm.IR iregd) (sign_add (s (Asm.IR iregd)) (s (Asm.IR ireg2))) s
    end.

  (* Why is `astate` (abstract state) from the AbstractInterpreter definition unavailable. *)
    Definition astate := x86ISA.regmap.t t.

    (* Abstract semantics of x86 instructions *)
    Definition empty_astate := x86ISA.regmap.init top. 

    Definition state_eq (s1 s2 : astate) : bool :=
      let fix compare_keys ks := match ks with
                                | nil => true
                                | k :: ks' => let v1 := get k s1 in
                                              let v2 := get k s2 in
                                if SignAbstractDomain.eq v1 v2 then compare_keys ks' else false
                                end
      in compare_keys x86ISA.reglist.

    (* Join abstract state *) 
    Definition join_state (s1 s2 : astate) : astate :=
      let all_keys := x86ISA.reglist in
      let fix build_state keys :=
      match keys with
      | nil => empty_astate
      | k :: ks => let v1 := get k s1 in
                  let v2 := get k s2 in
                  let rest := build_state ks in
                  set k (join v1 v2) rest
      end in
      build_state all_keys.


    (* Semantics of abstract instructions *) 
    Fixpoint abs_interp (c:x86ISA.code) (s:astate) : astate :=
      match c with
      | nil => s
      | i :: code' => abs_interp code' (aexec_instr i s)
      end.
End x86SignAbstractInterpreter.

Import x86SignAbstractInterpreter.

Print instruction'.
Definition program1 := [Pmovl_ri' Asm.RAX (Int.repr 3); Pmovl_ri' RBX (Int.repr 4); Paddl_rr' RAX RBX; Pmovl_ri' Asm.RBX (Int.zero)].

Definition final_state := Eval vm_compute in abs_interp program1 empty_astate.

Compute get (Asm.IR Asm.RAX) final_state. (* Pos  *)
Compute get (Asm.IR Asm.RBX) final_state. (* Zero *)
Compute get (Asm.IR Asm.RCX) final_state. (* Top  *)







Module Type Abstract_Domain_Picinae (Arch: Architecture) (CORE: PICINAE_CORE Arch).
  Import CORE.
  (* We get:
        - Var - the decidable type enumerating all registers
        - typctx - the type `var -> option bitwidth`
        - archtyps - a typctx mapping all vars to their bitwidths
        - exp - Picinae's abstract syntax for expressions (12 constructors)
        - stmt - the abstract syntax for statements (7 constructors)

     Furthermore we have
        - unop_typ - the syntax of unary operations (4 constructors)
        - binop_typ - the syntax of binary operations (19 constructors)
        - cast_typ - the syntax of cast operations (4 constructors)
   *)

  Parameter t : Type.
  Parameter top : t.
  Parameter eq : t -> t -> bool.
  Parameter join : t -> t -> t. (* least upper bound *)
  Parameter intersect : t -> t -> t. (* greatest lower bound *)
  Definition astate := Var.t -> t.

  Parameter auop : unop_typ -> t -> t -> Prop.
  Parameter abop : binop_typ -> t -> t -> t -> Prop.
  Parameter acop : cast_typ -> N -> t -> t -> Prop.

  Parameter aeval_exp : typctx -> astate -> exp -> t -> Prop.
  (* option exit specifies the next address to execute (if it is None) or a hardware interrupt *)
  Parameter aexec_stmt : typctx -> astate -> stmt -> typctx -> astate -> option exit -> Prop.

  (* Concretization function *)
  Parameter to_con : t -> (int64 -> Prop).
  (* Abstraction function *)
  Parameter to_abs : int64 -> t.
End Abstract_Domain_Picinae.
