(* SMEDL Abstract Syntax with type elaborations. *)
Inductive Ty : Set :=
| SBool : Ty
| SInt : Ty
| SFloat : Ty
| SProduct : Ty -> Ty -> Ty.
