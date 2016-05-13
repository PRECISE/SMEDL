Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith.
Require Import Types.

Open Scope type. 

Fixpoint compile_type (t : Ty) : Type :=
  match t with
  | SBool => bool
  | SInt => nat
  | SFloat => Q
  | SProduct t1 t2 => compile_type t1 * compile_type t2
  end.