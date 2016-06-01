Require Import Coq.Lists.List.
Require Import Coq.Program.Program.

(** Helper that should be in list. Filters using sumbools instead of using
bools, and keeps the evidence around. *)
Program Fixpoint filter_sumbool
        {a : Type}
        {P : a -> Prop}
        (p : forall (x : a), { P x } + { ~P x })
        (xs : list a) :
  list { x : a | P x } := 
  match xs with
  | nil => nil
  | (x::xs') =>
    match p x with
    | in_left => x :: filter_sumbool p xs'
    | in_right => filter_sumbool p xs'
    end
  end.

(** Type for representing two non-exclusive possibilities. Useful for tracking
warnings vs errors.

API borrowed from
 http://hackage.haskell.org/package/these-0.4.1/docs/Control-Monad-Trans-Chronicle.html
with some tweaks to be more idiomatic for Coq.
 *)

Inductive These (a b : Type) : Type :=
| These_this : a -> These a b
| These_that : b -> These a b
| These_these : a -> b -> These a b.

Arguments These_that {_ _} _.
Arguments These_this {_ _} _.
Arguments These_these {_ _} _ _.

(** Non-dependent case analysis. *)
Definition these {a b c : Type} : 
  (a -> c) -> (b -> c) -> (a -> b -> c) -> (These a b) -> c :=
  These_rect a b (fun _ => c).

Definition fromThese {a b : Type} (xa : a) (xb : b) :
  These a b -> a * b :=
  these (flip pair xb) (pair xa) pair.

Definition mergeThese {a : Type} : (a -> a -> a) -> These a a -> a :=
  these id id.

Definition isThisP {a b : Type} (x : These a b) : Prop :=
  exists (xa : a), x = These_this xa.

(* Program Definition isThis {a b : Type} (x : These a b) : *)
(*   { isThisP x } + { ~ isThisP x } := *)
(*   match x with *)
(*   | These_this xa => in_left *)
(*   | _ => in_right *)
(*   end. *)
(* Obligation 1. *)
(* unfold isThisP; eauto. *)
(* Qed. *)
(* Obligation 2. *)
(* firstorder congruence. *)
(* Qed. *)

(* Program Definition fromThis {a b : Type} (x : {x : These a b | isThisP x}) : a := *)
(*   match x with *)
(*   | These_this xa => xa *)
(*   | _ => _ *)
(*   end. *)
(* Obligation 1. *)
(* exfalso. *)
(* inversion H0. *)
(* eapply H. *)
(* eauto. *)
(* Qed. *)

(* Program Definition catThis {a b} : list (These a b) -> list a := *)
(*   map fromThis ∘ filter_sumbool isThis. *)

Definition Chronicle c a := These (list c) a.

(** dictate c is an action that records the output c. *)
Definition dictate {c} (xc : c) : Chronicle c () :=
  These_these [xc] ().

(** confess c is an action that ends with a final output c. *)
Definition confess {c a} (xc : c) : Chronicle c a :=
  These_this [xc].

(** memento m is an action that executes the action m, returning either its
record if it ended with confess, or its final value otherwise, with any record
added to the current record. *)
Definition memento {c a} (x : Chronicle c a) : Chronicle c (list c + a) :=
  match x with
  | These_this xc => These_that (inl xc)
  | These_that xa => These_that (inr xa)
  | These_these xc xa => These_these xc (inr xa)
  end.

(** absolve x m is an action that executes the action m and discards any record
it had. The default value x will be used if m ended via confess. *)
Definition absolve {c a} (xa : a) (x : Chronicle c a) : (Chronicle c a) :=
  match x with
  | These_this _ => These_that xa
  | These_these _ xa' => These_that xa'
  | These_that xa' => These_that xa'
  end.

(** condemn m is an action that executes the action m and keeps its value only if
it had no record. Otherwise, the value (if any) will be discarded and only the
record kept.

This can be seen as converting non-fatal errors into fatal ones. *)
Definition condemn {c a} (x : Chronicle c a) : Chronicle c a :=
  match x with
  | These_this xc => These_this xc
  | These_these xc _ => These_this xc
  | These_that xa => These_that xa
  end.

(** retcon f m is an action that executes the action m and applies the function
f to its output, leaving the return value unchanged. *)
Definition retcon {c a} (f : list c -> list c) (x : Chronicle c a) : Chronicle c a :=
  match x with
  | These_this xc => These_this (f xc)
  | These_that xa => These_that xa
  | These_these xc xa => These_these (f xc) xa
  end.

(** Monad operations *)

(** Monadic return *)
Definition ret {c a} (xa : a) : Chronicle c a := These_that xa.

(** Monadic bind *)
Definition bind {c a b : Type}
           (x : Chronicle c a)
           (f : a -> Chronicle c b) : Chronicle c b :=
  match x with
  | These_this xc => These_this xc
  | These_that xa => f xa
  | These_these xc xa =>
    match f xa with
    | These_this xc' => These_this (app xc xc')
    | These_that xa' => These_these xc xa'
    | These_these xc' xa' => These_these  (app xc xc') xa'
    end
  end.

Notation "'do' x <- m ; y" :=
  (bind m (fun x => y))
    (at level 60, right associativity).

Notation "'do' ( x1 , x2 ) <- m ; y" :=
  (bind m (fun z => let (x1, x2) := z in y))
    (at level 60, right associativity).

Notation "'do' ( x1 , x2 , x3 ) <- m ; y" :=
  (bind m (fun z => let (x1, x2, x3) := z in y))
    (at level 60, right associativity).