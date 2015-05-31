(*
*  program : specification : Set
*  proof   : statement     : Prop
*
*  program/proof is verified by a type checking algoritm
*)

(* loads definitions, theorems, notations into global environmest *)
Require Import Arith.
Require Import ZArith.
Require Import Bool.

(* interpretation of overloaded notations *)
Open Scope Z_scope.

Locate "_ * _".
(*
    "x * y" := prod x y  : type_scope
    "x * y" := Pos.mul x y : positive_scope
    "n * m" := mult n m  : nat_scope
    "x * y" := Z.mul x y : Z_scope (default interpretation)
    "x * y" := N.mul x y : N_scope 
*)

(* more information about a scope *)
Print Scope Z_scope.

(* type checking *)
Check 0.     (* 0 : Z *)
Check 0%nat. (* 0%nat : nat *)
Check O.     (* O : nat, O is a constructor of nat datatype *)
Check 35.    (* 35 : Z *)

Open Scope nat_scope.
Check 0.     (* 0 : nat *)
Check 35.    (* 35 : nat *)
Check -35%Z. (* -35%Z : Z, it would not type check without Z delimination *)

Check true.  (* true : bool, true is a constructor of bool datatype *)
Check false. (* false : bool *)


