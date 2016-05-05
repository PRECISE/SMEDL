Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.QArith.QArith.

Open Scope type. 

(* SMEDL Abstract Syntax *)
Module AST.
  Inductive SType : Set :=
  | SInt : SType
  | SFloat : SType
  | SProduct : SType -> SType -> SType.

  Inductive BinOp : Set :=
  | And : BinOp
  | Or : BinOp
  | Plus : BinOp
  | Times : BinOp
  | Eq : BinOp.

  Inductive UnOp : Set :=
  | Not : UnOp 
  | Neg : UnOp.

  Inductive Expr : Set :=
  | BoolLit : bool -> Expr
  | IntLit : nat -> Expr
  | BinOpExpr : BinOp -> Expr -> Expr -> Expr
  | UnOpExpr : UnOp -> Expr -> Expr.

  Inductive Cmd : Set := 
  | Assign : string -> Expr -> Cmd
  | Raise : string -> list Expr -> Cmd.

  Record Transition :=
    { transSrc : string;
      transParam : list string;
      transGuard : Expr;
      transAction : Cmd;
      transDest : string;
    }.

  Record Monitor :=
    { monState : list (string * SType);
      monEvent : list (string * list SType);
      monScenarios : list (string * list Transition);
    }.
End AST.

Module Machine.
  Record Transition {s : Type} {e : Type} := mkTransition
    { source : s;
      event : e;
      output : list e;
      destination : s;
    }.

  Arguments mkTransition {_} {_} _ _ _ _.

  (* Semantics *)
  Record FSM := mkFSM
    { fsmState : Type;
      fsmEvent : Type;
      fsmTransitions :> @Transition fsmState fsmEvent -> Type;
    }.

  Definition full_trace (fsm : FSM) :=
    list (@Transition (fsmState fsm) (fsmEvent fsm)).

  Inductive FullTrace : forall (fsm : FSM), full_trace fsm -> Type :=
  | FullTrace_Empty fsm : FullTrace fsm nil
  | FullTrace_Step fsm : forall s s' s'' e e' es es' ts,
      FullTrace fsm (mkTransition s e es s'::ts)
      -> fsm (mkTransition s e es s')
      -> FullTrace fsm (mkTransition s' e' es' s''::
                                     mkTransition s e es s'::
                                     ts).

  Fixpoint extract (fsm : FSM) (tr : full_trace fsm) : list (fsmEvent fsm) :=
    match tr with
    | nil => nil
    | t::tr' => app (output t) (extract fsm tr')
    end.

  Definition Produces (fsm : FSM) (es : list (fsmEvent fsm)) : Type :=
    exists tr, extract fsm tr = es.
End Machine.


Fixpoint compile_type (t : AST.SType) : Type :=
  match t with
  | AST.SInt => nat
  | AST.SFloat => Q
  | AST.SProduct t1 t2 => compile_type t1 * compile_type t2
  end.

Require Import Coq.FSets.FMaps.

Module M.
  Definition t := string.
  Definition eq_dec := String.string_dec.
End M.
Module M' := Make_UDT(M).
Module M'' := Coq.Structures.Equalities.Backport_DT(M').
Module SMap := FMapWeakList.Make(M'').

Definition tenv := SMap.t Type.
Definition tempty := SMap.empty Type.
Definition tadd := @SMap.add Type.

(* Needs check for uniqueness of names. *)
Fixpoint compile_state_decls (ss : list (string * AST.SType)) : tenv :=
  match ss with
  | nil => tempty
  | (n, t)::ss' => tadd n (compile_type t) (compile_state_decls ss')
  end.
(*
Definition lookup (m : tenv) (k : { key : string | SMap.In key m }) : Type.
  Search (SMap.t).
  assert (exists x, SMap.MapsTo (proj1_sig k) Type x).
  Search SMap.MapsTo.
  Search SMap.In.
  Search SMap.mem.
  unfold SMap.In in k.
  apply SMap.elements_2 in 
  forall (elt : Type) (m : SMap.t elt)
    (x : SMap.key) (e : elt),
  InA (SMap.eq_key_elt (elt:=elt)) 
    (x, e) (SMap.elements (elt:=elt) m) ->
  SMap.MapsTo x e m
  unfold SMap.Raw.PX.MapsTo.
  assert (x : SMap.find (proj1_sig k) m).
  

Record Emap :=
  { enum : list string;
    f : string -> Type;
    lookup : forall (key : {k : string | In k enum}), f (proj1_sig key)
    update : forall (key : {k : string | In k enum}), f (proj1_sig key) -> EMap
  }.
  enum : k -> Prop := fun k => In [] k.
Module Type EMap.
  Parameter k : Type.
  Parameter v : Type.
  Parameter t : Type.
  Parameter enum : k -> Prop.
  Parameter init : t.
  Parameter lookup : { key : k | enum key } -> t -> v.
  Parameter update : { key : k | enum key } -> t -> v -> t.
End EMap.
*)
(* Dependent map using types from compile_state_decls, combined with proof of
key membership.

This requires a check that the state names are non-conflicting. *)
Parameter compile_state : AST.Monitor -> Type.

(* Tagged sum of dependent maps. Tags are the names of the events. Dependent
maps are from event parameters to compiled smedl types.

This requires a check that the event names are non-conflicting and that the
event parameter names are non-conflicting.
*)
Parameter compile_event : AST.Monitor -> Type.

(* No idea. *)
(* A monitor's state machine should be the synchronous product of the state
machines of its scenarios. There will need to be static checks to make sure that
  1. The commands and guards type check w.r.t. the state and event types.
  2. The commands in the product machine are compatible (i.e. no contradictory
     updates). *)
Parameter compile_transitions : forall (m : AST.Monitor) (tr : @Machine.Transition (compile_state m) (compile_event m)), Type.

Definition semantics (m : AST.Monitor) : Machine.FSM :=
  Machine.mkFSM (compile_state m) (compile_event m) (compile_transitions m).