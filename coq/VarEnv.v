Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles.
Require Import SMEDL.Types.

Arguments In {_} _ _.
Arguments Add {_} _ _ _.

(** Variable environments *)
Record t : Type := make
  { vars : Ensemble string;
    lookup : {v : string | In vars v} -> Ty;
  }.

Module Coercions.
  Coercion VarEnv_var (Γ : t) : Set :=
    {n : string | In (vars Γ) n}.

  Coercion VarEnv_var_name {Γ : t} (v : Γ) : string :=
    proj1_sig v.
End Coercions.
Export Coercions.

Program Definition extend (Γ : t) (n : string) (x : Ty) : t :=
  make (Add (vars Γ) n)
           (fun v => if string_dec (proj1_sig v) n
                     then x
                     else (lookup Γ v)).
Obligation 1.
inversion H0; subst.
- assumption.
- inversion H1.
  congruence.
Qed.

Module Notations.
  Notation "v ∈ Γ" := (In (vars Γ) v) (at level 40).

  Notation "Γ [ v ]" := (lookup Γ v) (at level 40).

  Notation "Γ +[ v ; ty ]" := (extend Γ v ty) (at level 40).
End Notations.
Export Notations.

Program Definition remove (Γ : t) (v : Γ) : t :=
  make (Subtract _ (vars Γ) v)
       (fun v' => lookup Γ v').
Obligation 1.
destruct H.
exact H.
Defined.

Program Definition weaken_var {Γ : t} {v : Γ} (v' : remove Γ v) : Γ :=
   v'.
Obligation 1.
destruct v' as [? H].
destruct H as [H ?].
exact H.
Defined.
