(* Abstract interpretation of signedness of a simple while-language. 

   By Priya Swarn
   Adapted to depending on Compcert by Ilan Buzzetti
 *)
Require Import compcert.lib.Coqlib Wlang Sign.
From compcert Require Import Maps Errors Integers.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Module Type Abstract_Domain.
Parameter t : Type.
Parameter top : t.
Parameter eq : t -> t -> bool.
Parameter join : t -> t -> t. (* least upper bound *)
Parameter intersect : t -> t -> t. (* greatest lower bound *)
(*Parameter widen : t -> t -> t. (* widening *)
  Parameter narrow : t -> t -> t. (* narrowing *) *)

(* Abstract operators *)
Parameter aplus : t -> t -> t.
Parameter asub : t -> t -> t.
Parameter amult : t -> t -> t.

(* Abstract boolean operators *)
Parameter alt : t -> t -> t.
Parameter altu : t -> t -> t.
Parameter agt : t -> t -> t.
Parameter agtu : t -> t -> t.
Parameter aeq : t -> t -> t.
Parameter aand : t -> t -> t.
Parameter aor : t -> t -> t.

(* Concretization function *)
Parameter to_con : t -> (int64 -> Prop).
(* Abstraction function *)
Parameter to_abs : int64 -> t.


End Abstract_Domain.

Module Abi(Ab : Abstract_Domain).
Import Ab.

(* Abstract state is map from index(var) to abstract domain *)
Definition ab_state := PTree.t Ab.t.

Fixpoint keys_union (l1 l2 : list positive) : list positive :=
match l1 with
| nil => l2
| x :: xs => if List.existsb (fun y => Pos.eqb x y) l2 
             then keys_union xs l2 
             else x :: keys_union xs l2
end.

Definition state_eq (s1 s2 : ab_state) : bool :=
let keys1 := List.map fst (PTree.elements s1) in
let keys2 := List.map fst (PTree.elements s2) in
let all_keys := keys_union keys1 keys2 in
let fix compare_keys ks := match ks with
                           | nil => true
                           | k :: ks' => let v1 := match PTree.get k s1 with 
                                                   | Some v => v 
                                                   | None => top end in
                                         let v2 := match PTree.get k s2 with 
                                                   | Some v => v 
                                                   | None => top end in
                           if Ab.eq v1 v2 then compare_keys ks' else false
                          end
in compare_keys all_keys.

(* Join abstract state *) 
Definition join_state (s1 s2 : ab_state) : ab_state :=
let keys1 := List.map fst (PTree.elements s1) in
let keys2 := List.map fst (PTree.elements s2) in
let all_keys := keys_union keys1 keys2 in
let fix build_state keys :=
match keys with
| nil => PTree.empty Ab.t
| k :: ks => let v1 := match PTree.get k s1 with
                       | Some v => v 
                       | None => top end in
             let v2 := match PTree.get k s2 with 
                       | Some v => v 
                       | None => top end in
             let rest := build_state ks in
             PTree.set k (join v1 v2) rest
end in
build_state all_keys.


(* Semantics of abstract expressions *) 
Fixpoint asem_expr (ab_s : ab_state) (ae : Wlang.expr) {struct ae} : res Ab.t :=
match ae with 
| Const z => OK (to_abs z)
| Var x => match (PTree.get x ab_s) with 
           | Some z => OK z
           | None => Error (msg "Variable not found")
           end
| Bop o ae1 ae2 => match o with 
                   | Add => do v1 <- (asem_expr ab_s ae1);
                            do v2 <- (asem_expr ab_s ae2);
                            OK (Ab.aplus v1 v2)
                   | Minus => do v1 <- (asem_expr ab_s ae1);
                              do v2 <- (asem_expr ab_s ae2);
                              OK (Ab.asub v1 v2) 
                   | Mul => do v1 <- (asem_expr ab_s ae1);
                            do v2 <- (asem_expr ab_s ae2);
                            OK (Ab.amult v1 v2)
                   | Lt => do v1 <- (asem_expr ab_s ae1);
                           do v2 <- (asem_expr ab_s ae2);
                           OK (Ab.alt v1 v2)
                   | Ltu => do v1 <- (asem_expr ab_s ae1);
                            do v2 <- (asem_expr ab_s ae2);
                            OK (Ab.altu v1 v2)
                   | Gt => do v1 <- (asem_expr ab_s ae1);
                           do v2 <- (asem_expr ab_s ae2);
                           OK (Ab.agt v1 v2)
                   | Gtu => do v1 <- (asem_expr ab_s ae1);
                            do v2 <- (asem_expr ab_s ae2);
                            OK (Ab.agtu v1 v2)
                   | Eq => do v1 <- (asem_expr ab_s ae1);
                           do v2 <- (asem_expr ab_s ae2);
                           OK (Ab.aeq v1 v2)
                   | And => do v1 <- (asem_expr ab_s ae1);
                            do v2 <- (asem_expr ab_s ae2);
                            OK (Ab.aand v1 v2)
                   | Or => do v1 <- (asem_expr ab_s ae1);
                           do v2 <- (asem_expr ab_s ae2);
                           OK (Ab.aor v1 v2)
                   end
end.

(* Semantics of abstract instructions *) 
Definition limit_fixpoint := S (S (S (S (S (S (S (S (S (S O))))))))).
Fixpoint abs_interp (ab_s : ab_state) (ai : Wlang.instr) (fuel : nat) {struct fuel} : res ab_state :=
match fuel with 
| O => Error (msg "No fuel to suppprt")
| S f => match ai with 
         | Assgn (Var x) a => do v <- asem_expr ab_s a;
                              OK (PTree.set x v ab_s)
         | Assgn _ a => Error (msg "Can only be assigned to var")
         | Cond b i1 i2 => do s1 <- abs_interp ab_s i1 f;
                           do s2 <- abs_interp ab_s i2 f;
                           OK (join_state s1 s2)
         | While b i => let fix loop (n : nat) (acc : ab_state) : res ab_state :=
                        match n with
                        | O => OK acc
                        | S n' => do body_result <- abs_interp acc i f;
                                  let joined := join_state acc body_result in
                                  if state_eq acc joined (* check for convergence *)
                                  then OK joined
                                  else (loop n' joined)
                        end
                        in (loop limit_fixpoint ab_s) (* bounded fixpoint iteration *)
         | Seq i1 i2 => do s1 <- abs_interp ab_s i1 f;
                        abs_interp s1 i2 f
         | Skip => OK ab_s
         end
end.

End Abi.

Module Ad_sign <: Abstract_Domain.
Definition t := sign.
Definition top := Top.
Definition eq := eq_sign.
Definition join := join_sign.
Definition intersect := intersect_sign.
Definition aplus := sign_add.
Definition asub := sign_minus.
Definition amult := sign_mul.
Definition alt := sign_lt.
Definition altu := sign_ltu.
Definition agt := sign_gt.
Definition agtu := sign_gtu.
Definition aeq := sign_eq.
Definition aand := sign_and.
Definition aor := sign_or.
Definition to_con := Sign.to_con.
Definition to_abs := Sign.to_abs.

End Ad_sign.


(* Example *)
Module Example1 := Abi(Ad_sign).

Import Example1.

Definition x := 1%positive.
Definition y := 2%positive.
Definition z := 3%positive. 
(* We can set the initial state to whatever we like.  Here, `state` assumes all
   variables are initialized to zero.  Typically, a state like `topstate` would
   be used to say ``these variables may be *any* value to begin with.'' *)
Definition state := (PTree.set x Zero (PTree.set y Zero (PTree.set z Zero (PTree.empty sign)))).
Definition topstate := (PTree.set x Top (PTree.set y Top (PTree.set z Top (PTree.empty sign)))).

(* x = 1 ==> x : Pos *)
Definition test1 := Assgn (Var x) (Const (Int64.repr 1)).
Compute (do r <- abs_interp state test1 20;
         OK (PTree.get x r)).

(* x = 1; x = -5 ==> x : Neg *)
Definition test2 := Seq (Assgn (Var x) (Const (Int64.repr 1)))
                        (Assgn (Var x) (Const (Int64.repr (-5)))).
Compute (do r <- abs_interp state test2 20;
         OK (PTree.get x r)).

(* while (1 == 1) x = 0 ==> x : Zero *)
Definition test3 := While (Bop Eq (Const (Int64.repr 1)) (Const (Int64.repr 1)))
                          (Assgn (Var x) (Const (Int64.repr 0))).
Compute (do r <- abs_interp state test3 20;
         OK (PTree.get x r)).

(* y = 100; while (y > 0) { y = y-1; if y==0 then x = 0 else skip } ==> x : Zero *)
Definition test3' := Seq (Assgn (Var y) (Const (Int64.repr 5))) (While (Bop Gt (Var y) (Const (Int64.repr 0)))
                          (Seq (Assgn (Var y) (Bop Minus (Var y) (Const (Int64.repr 1)))) (Cond (Bop Eq (Var y) (Const (Int64.repr 0))) (Assgn (Var x) (Const (Int64.repr 0))) (Skip)))).
Compute (do r <- abs_interp state test3' 20;
         OK (PTree.get x r)).

(* while (1 == 1) x = 1; x = x + 1 ==> x : Pos? No... Top! Why?

   This abstract domain alone is too weak to determine if loops can or must
   execute at least once. First of all, it does not consider the conditions of while
   loops nor conditionals. Second, if it did it would only be able to determine if
   they cannot run by seeing whether their condition is necessarily Zero.
   Thus, because the loop may or may not run, `x` may be Zero (the initial value) or Pos.
   Their join is Top, so our algorithm says `Top`.
*)
Definition test4 := While (Bop Eq (Const (Int64.repr 1)) (Const (Int64.repr 1)))
                          (Seq (Assgn (Var x) (Const (Int64.repr 1)))
                               (Assgn (Var x) (Bop Add (Var x) (Const (Int64.repr 1))))).
Compute (do r <- abs_interp state test4 3;
         OK (PTree.get x r)).

(* x = 2 + 1 ==> x : Pos *)
Definition test5 := Assgn (Var x) (Bop Add (Const (Int64.repr 2)) (Const (Int64.repr 1))).
Compute (do r <- abs_interp state test5 20;
         OK (PTree.get x r)).

(* while (1 == 1) x = 1; x = 2 ==> x : Top (see test4) *)
Definition test6 := While (Bop Eq (Const (Int64.repr 1)) (Const (Int64.repr 1)))
                          (Seq (Assgn (Var x) (Const (Int64.repr 1)))
                               (Assgn (Var x) (Const (Int64.repr 2)))).
Compute (do r <- abs_interp state test6 20;
         OK (PTree.get x r)).

(* x = x + 1 ==> x : Pos *)
Definition test7 := Assgn (Var x) (Bop Add (Var x) (Const (Int64.repr 1))).
Compute (do r <- abs_interp state test7 20;
         OK (PTree.get x r)).

(* x = 5; x = x + (-3) ==> x : Top *)
Definition test8 :=
  Seq (Assgn (Var x) (Const (Int64.repr 5)))
      (Assgn (Var x) (Bop Add (Var x) (Const (Int64.repr (-3))))).
Compute (do r <- abs_interp state test8 20;
         OK (PTree.get x r)).


(* x = (x - 3) + 4 ==> x : Pos *)
Definition test9 :=
     (Assgn (Var x) (Bop Add (Bop Minus (Var x) (Const (Int64.repr (-3)))) (Const (Int64.repr (4))))).
Compute (do r <- abs_interp state test9 20;
         OK (PTree.get x r)).

(* x = 5; x = x + x ==> x : Pos *)
Definition test10 :=
  Seq (Assgn (Var x) (Const (Int64.repr 5)))
      (Assgn (Var x) (Bop Add (Var x) (Var x))).
Compute (do r <- abs_interp state test10 20;
         OK (PTree.get x r)).

(* x = 5; x = x - x ==> x : Zero? No... Top! Why?

  This algorithm only remembers the sign of expressions, it does not reason
  about their value. Thus when it reasons about the sign of `x - x` what it
  really sees is `Pos - Pos`. Because this can be positive, negative or zero
  it returns Top.
*)
Definition test11 :=
  Seq (Assgn (Var x) (Const (Int64.repr 5)))
      (Assgn (Var x) (Bop Minus (Var x) (Var x))).
Compute (do r <- abs_interp state test11 20;
         OK (PTree.get x r)).

(* x = x - x; x = x - 4 ==> x : Neg *)
Definition test12 :=
  Seq (Assgn (Var x) (Bop Minus (Var x) (Var x)))
      (Assgn (Var x) (Bop Minus (Var x) (Const (Int64.repr 4)))).
Compute (do r <- abs_interp state test12 20;
         OK (PTree.get x r)). 

(* if (1) then x = 5 else x = -5 ==>  x : Top *)
Definition cond_test1 :=
  Cond (Const Int64.one)
       (Assgn (Var x) (Const (Int64.repr 5)))
       (Assgn (Var x) (Const (Int64.repr (-5)))).
Compute (do r <- abs_interp state cond_test1 20;
         OK (PTree.get x r)). 

(* x = 5; y = -3; z = x + y ==> x : Pos, y : Neg, z : Top*)
Definition multi_add1 :=
  Seq (Assgn (Var x) (Const (Int64.repr 5)))
      (Seq (Assgn (Var y) (Const (Int64.repr (-3))))
           (Assgn (Var z) (Bop Add (Var x) (Var y)))).
Compute (do r <- abs_interp state multi_add1 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).

(* x = -10; y = -5; z = x + y ==> x : Neg, y : Neg, z : Neg *)
Definition multi_add2 :=
  Seq (Assgn (Var x) (Const (Int64.repr (-10))))
      (Seq (Assgn (Var y) (Const (Int64.repr (-5))))
           (Assgn (Var z) (Bop Add (Var x) (Var y)))).
Compute (do r <- abs_interp state multi_add2 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).

(* x = 0; y = 7; z = x - y ==> x : Zero, y : Pos, Z : Neg *)
Definition sub_zero_pos :=
  Seq (Assgn (Var x) (Const (Int64.repr (0))))
      (Seq (Assgn (Var y) (Const (Int64.repr (7))))
           (Assgn (Var z) (Bop Minus (Var x) (Var y)))).
Compute (do r <- abs_interp state sub_zero_pos 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).


(* x = -4; y = -2; z = x * y ==> x : Neg, y : Neg, Z : Pos *)
Definition mul_neg_neg :=
  Seq (Assgn (Var x) (Const (Int64.repr (-4))))
      (Seq (Assgn (Var y) (Const (Int64.repr (-2))))
           (Assgn (Var z) (Bop Mul (Var x) (Var y)))).
Compute (do r <- abs_interp state mul_neg_neg 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).

(* x = 0; z = x * 123 ==> x : Zero, y : Zero, z : Zero *)
Definition mul_zero :=
  Seq (Assgn (Var x) (Const (Int64.repr (0))))
      (Assgn (Var z) (Bop Mul (Var x) (Const (Int64.repr 123)))).
Compute (do r <- abs_interp state mul_zero 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).

(* x = 5; y = 2; z = x < y ==> x : Pos, y : Pos, z : Top *)
Definition lt_ex1 :=
  Seq (Assgn (Var x) (Const (Int64.repr (5))))
      (Seq (Assgn (Var y) (Const (Int64.repr 2)))
           (Assgn (Var z) (Bop Lt (Var x) (Var y)))).
Compute (do r <- abs_interp state lt_ex1 20;
         OK (PTree.get x r :: PTree.get y r :: PTree.get z r :: nil)).

(* x = 10; while (1) do x = x - 1 ==> x : Top *)
Definition loop_test1 := Seq (Assgn (Var x) (Const (Int64.repr 10)))
                             (While (Const (Int64.repr 1))
                                     (Assgn (Var x) (Bop Minus (Var x) (Const (Int64.repr 1))))).
Compute (do r <- abs_interp state loop_test1 20;
         OK (PTree.get x r)).
