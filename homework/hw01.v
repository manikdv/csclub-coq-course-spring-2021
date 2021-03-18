From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool :=
  match b with
  | true => true
  | false => c
  end.

Compute orb true true.
Compute orb true false.
Compute orb false true.
Compute orb false false.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool :=
  match b with
  | true => negb c
  | false => c
  end.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool :=
  match b with
  | true => c
  | false => negb c
  end.

Compute eqb false false.
Compute eqb false true.
Compute eqb true false.
Compute eqb true true.

(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat :=
  match n with
  | S (S n') => n'
  | _ => O
  end.

Compute dec2 (S (S (S O))).
Compute dec2 (S (S O)).
Compute dec2 (S O).


(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) {struct m} : nat :=
  match m with
  | S m' => match n with
            | S n' => subn m' n'
            | O => m
            end
  | O => m
  end.

Eval cbv beta delta iota in subn (S (S (S (S O)))) (S O).

Compute subn (S (S (S (S O)))) (S O).
Compute subn (S O) (S O).
Compute subn (S O) (S (S (S (S O)))).

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => addn (S m) n'
  end.

Fixpoint muln (m n : nat) : nat :=
  match n with
  | O => O
  | S n' => addn (muln m n') m
  end.

Compute muln O (S (S O)).
Compute muln (S (S O)) O.
Compute muln (S (S (S O))) (S (S O)).
Compute muln (S (S O)) (S (S (S O))).

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool :=
  match (m, n) with
  | (O, O) => true
  | (O, _) => false
  | (S m', O) => false
  | (S m', S n') => eqn m' n'
  end.

Compute eqn O O.
Compute eqn (S O) O.
Compute eqn O (S O).
Compute eqn (S O) (S O).
Compute eqn (S (S O)) (S O).
Compute eqn (S O) (S (S O)).
Compute eqn (S (S O)) (S (S O)).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq (m n : nat) : bool :=
  match subn m n with
  | S _ => false
  | _ => true
  end.

Compute leq O O.
Compute leq (S (S O)) (S O).
Compute leq (S O) (S (S O)).
Compute leq (S (S O)) (S (S O)).

(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

(* Fixpoint divn (m n : nat) {struct m} : nat := *)

(* Fixpoint subn' (m n : nat) {struct m} : nat :=
  if m is S m' then
    if n is S n' then S (subn' m' n') else m
  else m. *)

Fixpoint divn (m n : nat) : nat :=
  match n with
  | S n' => match subn m n' with
            | S m' => S (divn m' n)
            | O => O
            end
  | O => O
  end.

Definition n0 := O.
Definition n1 := S n0.
Definition n2 := S n1.
Definition n3 := S n2.
Definition n4 := S n3.
Definition n5 := S n4.
Definition n6 := S n5.
Definition n7 := S n6.
Definition n8 := S n7.
Definition n9 := S n8.
Definition n10 := S n9.


Check eq_refl : divn n9 n5 = n1.
Check eq_refl : divn n9 n4 = n2.

Check eq_refl : divn n0 n0 = n0.
Check eq_refl : divn n4 n2 = n2.
Check eq_refl : divn n3 n2 = n1.
Check eq_refl : divn n2 n2 = n1.
Check eq_refl : divn n2 n3 = n0.
Check eq_refl : divn n4 n0 = n0.
Check eq_refl : divn n0 n4 = n0.

End My.
