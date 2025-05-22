(* Abstract interpretation of signedness of a simple while-language. 

   By Priya Swarn
   Adapted to depending on Compcert by Ilan Buzzetti
 *)
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
From compcert Require Import AST Maps Globalenvs Ctypes Memory Cop.
From compcert Require Import Memtype Errors Csem SimplExpr Events Integers.
Require Import Coq.Arith.EqNat Coq.ZArith.Int compcert.lib.Coqlib Int.
From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Definition int64 := compcert.lib.Integers.int64.
Locate Int64.


Inductive bop : Type :=
| Add : bop
| Minus : bop
| Mul : bop
| Lt : bop
| Ltu : bop
| Gt : bop
| Gtu : bop
| Eq : bop
| And : bop
| Or : bop.

Inductive expr := 
| Const : int64 -> expr
| Var : positive -> expr
| Bop : bop -> expr -> expr -> expr.

Definition label := int64.

Inductive instr : Type :=
| Assgn : expr -> expr -> instr
| Cond : expr -> instr -> instr -> instr
| While : expr -> instr -> instr
| Seq : instr -> instr -> instr
| Skip : instr.

(* Values allowed in the program *)
Definition value := int64.

(* Map variables to Z *)
Definition state := PTree.t value.

Definition bool_int64 (b : bool) : int64  :=
match b with 
| true => Int64.one
| false => Int64.zero
end.

Fixpoint csem_expr (s : state) (a : expr) {struct a} : res value :=
match a with 
| Const z => OK z
| Var x => match PTree.get x s with 
           | Some v => OK v 
           | None => Error (msg "Variable not present")
           end
| Bop op a1 a2 => match op with 
                  | Add => do v1 <- csem_expr s a1;
                           do v2 <- csem_expr s a2;
                           OK (Int64.add v1 v2)
                  | Minus => do v1 <- csem_expr s a1;
                             do v2 <- csem_expr s a2;
                             OK (Int64.sub v1 v2)
                  | Mul => do v1 <- csem_expr s a1;
                            do v2 <- csem_expr s a2;
                            OK (Int64.mul v1 v2)
                  | Lt => do v1 <- csem_expr s a1;
                             do v2 <- csem_expr s a2;
                             OK (bool_int64 (Int64.lt v1 v2))
                  | Ltu => do v1 <- csem_expr s a1;
                           do v2 <- csem_expr s a2;
                           OK (bool_int64 (Int64.ltu v1 v2))
                  | Gt => do v1 <- csem_expr s a1;
                          do v2 <- csem_expr s a2;
                          OK (bool_int64 (Int64.lt v2 v1))
                  | Gtu => do v1 <- csem_expr s a1;
                           do v2 <- csem_expr s a2;
                           OK (bool_int64 (Int64.ltu v2 v1))
                  | Eq => do v1 <- csem_expr s a1;
                          do v2 <- csem_expr s a2;
                          OK (bool_int64 (Int64.eq v1 v2)) 
                  | And => do v1 <- csem_expr s a1;
                           do v2 <- csem_expr s a2;
                           OK (Int64.and v1 v2)
                  | Or => do v1 <- csem_expr s a1;
                          do v2 <- csem_expr s a2;
                          OK (Int64.or v1 v2)
                  end
end.
            
Fixpoint csem_instr (s : state) (i : instr) (fuel : nat) {struct fuel} : res state :=
match fuel with 
| O => Error (msg "No fuel to suppprt")
| S f => match i with 
         | Assgn (Var x) a => do v <- csem_expr s a;
                              OK (PTree.set x v s)
         | Assgn _ a => Error (msg "Can only be assigned to var")
         | Cond b i1 i2 => do v <- csem_expr s b;
                  if (Int64.eq v Int64.one) 
                  then csem_instr s i1 f 
                  else csem_instr s i2 f
         | While b i => do v <- csem_expr s b;
                        if (Int64.eq v Int64.one) 
                        then do s1 <- csem_instr s (While b i) f;
                             csem_instr s1 (While b i) f
                        else OK s
         | Seq i1 i2 => do s1 <- csem_instr s i1 f;
                        csem_instr s1 i2 f
         | Skip => OK s
         end             
end.
