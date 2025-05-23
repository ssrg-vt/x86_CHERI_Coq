(* Abstract interpretation of signedness of a simple while-language. 

   By Priya Swarn
   Adapted to depending on Compcert by Ilan Buzzetti
 *)
Require Import compcert.lib.Coqlib Wlang.
From compcert Require Import Errors Integers Maps.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Inductive sign : Type :=
| Bot : sign
| Pos : sign
| Neg : sign
| Zero : sign 
| Top : sign.

Definition sign_add (s1 s2 : sign) : sign :=
match s1, s2 with 
| Bot, _ | _, Bot => Bot
| Pos, Pos => Pos
| Neg, Neg => Neg 
| Pos, Neg => Top
| Neg, Pos => Top
| Zero, s => s
| s, Zero => s
| _, _ => Top
end. 

Definition neg_sign (s1 : sign) : sign :=
match s1 with 
| Bot => Bot
| Pos => Neg 
| Neg => Pos
| Zero => Zero
| Top => Top
end.

Definition sign_minus (s1 s2 : sign) : sign :=
match s1, s2 with
| Bot, _ | _, Bot => Bot
| Pos, Pos => Top
| Pos, Zero => Pos
| Pos, Neg => Top
| Zero, Pos => Neg
| Zero, Zero => Zero
| Zero, Neg => Pos
| Neg, Pos => Top
| Neg, Zero => Neg
| Neg, Neg => Top
| _, _ => Top
end.

Definition sign_mul (s1 s2 : sign) : sign :=
match s1, s2 with 
| Pos, Pos => Pos
| Neg, Neg => Pos 
| Pos, Neg => Neg
| Neg, Pos => Neg
| Zero, s => Zero
| s, Zero => Zero
| _, _ => Top
end.  

Definition sign_lt (s1 s2 : sign) : sign := Top.
Definition sign_ltu (s1 s2 : sign) : sign := Top.
Definition sign_gt (s1 s2 : sign) : sign := Top.
Definition sign_gtu (s1 s2 : sign) : sign := Top.
Definition sign_eq (s1 s2 : sign) : sign := Top.
Definition sign_and (s1 s2 : sign) : sign := Top.
Definition sign_or (s1 s2 : sign) : sign := Top.

Definition eq_sign (s1 s2 : sign) : bool :=
match s1, s2 with 
| Bot, Bot => true
| Neg, Neg => true 
| Pos, Pos => true 
| Zero, Zero => true 
| Top, Top => true
| _, _ => false
end.

Definition join_sign (s1 s2 : sign) : sign :=
match s1, s2 with 
| Bot, s | s, Bot => s
| Pos, Pos => Pos
| Neg, Neg => Neg
| Zero, Zero => Zero
| _, _ => Top
end.

Definition intersect_sign (s1 s2 : sign) : sign :=
match s1, s2 with
| Bot, x | x, Bot => Bot
| Top, x | x, Top => x
| Pos, Pos => Pos
| Neg, Neg => Neg
| Zero, Zero => Zero
| _, _ => (* they disagree *) Bot
end.

(* If the new value equals the old one, keep it; otherwise, go to Top. *)
Definition widen_sign (old new : sign) : sign :=
match old, new with
| Bot, Bot => Bot
| Pos, Pos => Pos
| Neg, Neg => Neg
| Zero, Zero => Zero
| _, _ => Top
end.

(* If we overshot to Top but the new value is more precise, accept it. *)
Definition sign_narrow (old new : sign) : sign :=
match old, new with
| Top, Bot => Bot
| Top, Pos => Pos
| Top, Neg => Neg
| Top, Zero => Zero
| _, _ => old
end.

Definition to_abs (i : int64) : sign :=
if Integers.Int64.lt i Integers.Int64.zero 
then Neg
else if Integers.Int64.lt Integers.Int64.zero i
     then Pos
     else if Integers.Int64.eq i Integers.Int64.zero
          then Zero
          else Top.

Definition to_con (s : sign) : int64 -> Prop :=
match s with 
| Bot => fun i => False
| Pos => fun i => Integers.Int64.lt Integers.Int64.zero i
| Neg => fun i => Integers.Int64.lt i Integers.Int64.zero
| Zero => fun i => Integers.Int64.eq i Integers.Int64.zero
| Top => fun i => True
end.
