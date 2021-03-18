From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:=
  fun '(a, b, c) => (a, (b, c)).

Compute prodA nat nat nat.

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=
  fun tt =>
    match tt with
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:=
  fun tt =>
    match tt with
    | (a, inl b) => inl (a, b)
    | (a, inr c) => inr (a, c)
    end.

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:=
  fun tt =>
    match tt with
    | inl a => (inl a, inl a)
    | inr (b, c) => (inr b, inr c)
    end.

(* function composition *)
Definition comp {A B C : Type} (f : B -> A) (g : C -> B) : C -> A
:= fun tt => f (g tt).

(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)

Notation "f \o g" :=
  (comp f g) (at level 90, left associativity)
  : type_scope.

Variables a b : Type -> Type.
Compute a \o b.

(* Introduce empty type, call `void` *)

Inductive void := .
About void.

Definition void_terminal (A : Type) :
  void -> A
:= fun tt => match tt with end.

Compute void_terminal void.

(* Introduce `unit` type (a type with exactly one canonical form) *)

Inductive unit : Type := u.

Definition unit_initial (A : Type) :
  A -> unit
:= fun tt => u.


(* Think of some more type signatures involving void, unit, sum, prod *)
