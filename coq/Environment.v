(** Library for capturing evaluation environments. *)
Require Import Coq.Lists.List.
Open Scope type.
Open Scope list.

(** Type of co-domain of environment. *)
Parameter codom: Type.

(** Underlying type of variables. *)
Parameter var : Set.

(** Variables must have decidable equality. *)
Parameter var_dec : forall (v1 v2 : var), { v1 = v2 } + { v1 <> v2 }.

(** Unlike [Coq.Lists.List.In], this values of this [In] type are extensional
because they always refer to the first element in the list that [v] equals.*)
Inductive In {A : Type} (v : A) : list A -> Prop :=
| In_hd : forall vs, In v (v :: vs)
| In_tl : forall vs v', v <> v' -> In v vs -> In v (v'::vs).

Hint Constructors In.

Set Printing Implicit.

Lemma In_extensional : forall (v : var) (vs : list var) (H1 H2 : In v vs),
    H1 = H2. 
Proof.
  induction vs; intros.
  - inversion H1.
  - destruct (var_dec v a).
    subst.
    destruct H1.
    generalize 
    destruct H2.
  i
  destruct H1.
  intros.
  destruct H2.

  - 
  - destruct H1.
    + destruct H2. exfalso.

    destruct H1.
    destruct H2 eqn:H2'.
    
    + subst.
      simpl in *.

  -
    inversion H1; inversion H2.
    subst.
    inversion H2.
  

(** An environment maps a finite subset of variables to values. *)
Definition Env := { dom : list var & {v | In v dom} -> a}.

(** A variable that is bound by an environment has a mapping in that environment. *)
Definition Bound (env : Env) (v : var) : Prop :=
  let (dom, _) := env in In v dom.

Parameter lookup : Bound var -> a.
Inductive Env