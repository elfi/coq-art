(******************************************************************)
(** 1.3 Proposition as types **)
(*
    program : specification : Set
    proof   : statement     : Prop

    program/proof is verified by a type checking algoritm
*)

(******************************************************************)
(** 2.1 First steps **)
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

(******************************************************************)
(** 2.2 The rules of the game **)
(*
    declaration - attaches a type to an identifier  (x : A)
    definition  - attaches a value to an identifier (x := t : A)

    commands: Reset Initial.
              Reset 'id'.
*)

(* Identifiers *)
(*
    To express that a variable x is declared with type A in a context
    Gamma we use notation (x:A) \in Gamma.

    The notation Gamma \turnstile x : A reads "in the context Gamma,
    the term x has type A.

                (x:A) \in Gamma
    Var rule:   ---------------------
                Gamma \turnstile x:A

*)

Check plus. (* plus : nat -> nat -> nat *)
(*
    Check aaa.

    Error: The reference aaa was not found in the current environment.
*)

(* Function application *)
(*
                Gamma \turnstile e_1 : A -> B   Gammma \turnstile e_2 : A
    App rule:   ----------------------------------------------------------
                Gamma \turnstile e_1 e_2 : B

*)

Check negb.         (* negb : bool -> bool *)
Check (negb true).  (* negb true : bool *)

(* Natural numbers *)
(* All natural numbers are obtained via application of successor function S to
   the numeber zero represented by O.
   In the nat_scope the number is represented by its decimal value.
*)

Open Scope nat_scope.
Check (S (S (S O))).   (* 3 : nat *)
Check (mult 5 4).      (* 5 * 4 : nat *)
Check (5 * 4).         (* 5 * 4 : nat, infix notation supported by the scope *)

(* commands:
      Set Printing Notations.
      Unset Printing Notations.
*)

Open Scope Z_scope.
Check 7.            (* 7 : Z *)
Check (Zmult 3 4).  (* 3 * 4 : Z *)
Check (3 * 4).      (* 3 * 4 : Z *)

(* abstraction / notation for functions *)
(*
  gallina: fun n:nat => n*n
  lambda : \n:nat . n*n
  math   : n |-> n*n  : nat -> nat
  ocaml  : fun (n:nat) -> n*n

                Gamma :: (v:A) \turnstile e : B
    Lam rule:   -----------------------------------------
                Gamma \turnstile (fun v:A => e) : A -> B

     - e : B needs to be well typed in the extended context Gamma :: (v:A)
     - the formal parametr v:A plays a role of a local variable, whose scope is
       restricted inside the abstraction body
*)

(* nested abstraction *)
Check (fun n : nat => fun p : nat => fun z : Z => (Z_of_nat (n + p) + z)%Z).
Check (fun n p : nat => fun z : Z => (Z_of_nat (n + p) + z)%Z).
Check (fun (n p :nat) (z : Z) => (Z_of_nat (n + p) +z)%Z).

(*
  - if the type of a formal parameter can be determined from the body,
    it can be ommited
  - unused formal parameters are automatically replaced by anonymous variable _
*)

Check (fun a b : nat => a).  (* fun a _ : nat => a  : nat -> nat -> nat *)

(* local bindings *)
(* let v := t1 in t2 *)
Check (fun n p : nat =>
         (let diff := n - p in
          let square := diff * diff in
            square + p))%nat.

(* renaming of bound variables in abstractions and let-in bindings is
   a congruence called \alpha conversion *)

(******************************************************************)
(** 2.3 Declarations and definitions **)
(* Global declaration, Parameter v:A *)
Parameter  max_int : Z.   (* max_int is assumed *)

(* Global definition, Definition v:A := t
   - the type can be inferred
*)
Definition min_int := 1 - max_int.   (* min_int is defined *)
Print min_int.                       (* min_int = 1 - max_int : Z *)

(* Definition of functions - several syntactic form *)
Definition cube1 := fun z:Z => z*z*z.     (* explicit abstraction *)
Definition cube2 (z : Z) : Z :=  z*z*z.   (* passing type of input and output *)
Definition cube3 z :=  z*z*z.             (* just a name of parameter and body *)
Print cube3.
(*
  cube3 = fun z : Z => z * z * z
     : Z -> Z

  Argument scope is [Z_scope]       (* this is the last opened scope *)
*)



Open Scope nat_scope.
Check cube3.  (* cube3 : Z -> Z, the scope of/from the definition is remembered *)

(* Sections
   controlling scope of local variables

   local declaration: Variable a : A
   local definition:  Let x := t
*)

Open Scope Z_scope.

Section binomial_def.
    Variables a b : Z.
    Definition binomial z : Z := a*z + b.
    Print binomial.
    (*
       binomial = fun z : Z => a * z + b
         : Z -> Z

       a, b are in the context
    *)
    Section trinomial_def.
        Variable c : Z.
        Definition trinomial z : Z := (binomial z)*z + c.
    End trinomial_def.
End binomial_def.

(* all used local variables get added as an abstraction
   after section is closed - the variables are not any more
   available in the context and need to be added as formal
   parameters
*)
Print binomial.
(*
    binomial = fun a b z : Z => a * z + b
        : Z -> Z -> Z -> Z
*)

Print trinomial.
(*
    trinomial =
    fun a b c z : Z => binomial a b z * z + c
        : Z -> Z -> Z -> Z -> Z
*)


Section h_def.
    Variables a b : Z.
    Let s : Z := a + b.
    Let d : Z := a - b.
    Definition h : Z := s*s + d*d.
End h_def.

(* when section is closed local definitions are replaced
   with local let-in bindings
*)
Print h.
(*
    h =
    fun a b : Z => let s := a + b in let d := a - b in s * s + d * d
        : Z -> Z -> Z
*)


(******************************************************************)
(** 2.4 Computing **)
