import Basics

namespace IndProp

def div2 ( n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | n' + 2 => (div2 n').succ

def csf (n : Nat ) : Nat :=
  if even n then div2 n
  else (3*n) + 1

infix:70 " =? " => eqb

inductive Collatz_holds_for : Nat -> Prop where
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : Nat) :
        even n = true ->
        Collatz_holds_for (div2 n) ->
        Collatz_holds_for n
  | Chf_odd (n : Nat) :
        even n = false ->
        Collatz_holds_for (3*n + 1) ->
        Collatz_holds_for n


theorem Collatz_holds_for_12 : Collatz_holds_for 12 := by
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_odd
  rfl
  simp
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_odd
  rfl
  simp
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_even
  rfl
  simp [div2]
  apply Collatz_holds_for.Chf_one

-- In Lean Conjecture is not a keyword
-- we consider it as a definition for a proposition that we leave unproven

def collatz_conjecture_statement : Prop :=
  forall n, n != 0 -> Collatz_holds_for n

--  EXAMPLE : TRANSITIVE CLOSURE

inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop where
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X ) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z

inductive Person : Type where
  | Sage
  | Cleo
  | Ridley
  | Moss

open Person -- so that we can just type Sage instead of Person.Sage

inductive parent_of : Person -> Person -> Prop where
  | po_SC : parent_of Sage Cleo
  | po_SM : parent_of Sage Moss
  | po_CM : parent_of Cleo Moss

def ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of

example : ancestor_of Sage Moss := by
  unfold ancestor_of
  apply clos_trans.t_trans (y := Cleo)
  . apply clos_trans.t_step
    apply parent_of.po_SC
  . apply clos_trans.t_step
    apply parent_of.po_CM

inductive clos_refl_trans { X : Type } (R : X -> X -> Prop) : X -> X -> Prop where
  | rt_step (x y : X) : R x y -> clos_refl_trans R x y
  | rt_refl ( x : X) : clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z

def cs (n m : Nat) : Prop := csf n = m
#check cs

def cms n m := clos_refl_trans cs n m
#check cms

-- Exercise : symmetric closure

inductive clos_refl_trans_sym {X : Type} (R : X -> X -> Prop) : X -> X -> Prop where
  | rts_step (x y : X) : R x y → clos_refl_trans_sym R x y
  | rts_refl (x : X) : clos_refl_trans_sym R x x
  | rts_sym (x y : X) : clos_refl_trans_sym R x y → clos_refl_trans_sym R y x
  | rts_trans (x y z : X) :
      clos_refl_trans_sym R x y →
      clos_refl_trans_sym R y z →
      clos_refl_trans_sym R x z


-- We are going to use standard lean notation [a,b,c] instead of what [a;b;c] used in Coq

inductive Perm3 { X : Type } : List X -> List X -> Prop where
  | perm3_swap12 (a b c : X) : Perm3 [a,b,c] [b,a,c]
  | perm3_swap23 (a b c : X) : Perm3 [a,b,c] [a,c,b]
  | perm3_trans (l1 l2 l3 : List X) :
     Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3

inductive ev : Nat -> Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat)(H : ev n) : ev (n+2)

-- NOTE : S ( S n ) => n + 2 in Lean

open ev
theorem ev_4 : ev 4 := by
  apply ev_SS
  apply ev_SS
  apply ev_0

theorem ev_4' : ev 4 := by
  apply ev_SS 2 ( ev_SS 0 ev_0)

theorem ev_plus4 : ∀ n, ev n → ev (n + 4) :=
by
  intro n H
  -- change ev (Nat.succ (Nat.succ (Nat.succ ( Nat.succ n))))
  apply ev_SS
  apply ev_SS
  apply H

def double (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n' => Nat.succ (Nat.succ (double n'))

theorem ev_double : ∀ n, ev (double n) := by
  intro n
  induction n with
  | zero => simp [double]
            exact ev_0
  | succ n' IHn' =>
            simp [double]
            exact ev_SS (double n') IHn'

theorem Perm3_rev : Perm3 [1,2,3] [3,2,1] := by
  apply Perm3.perm3_trans (l2 := [2,3,1])
  . apply Perm3.perm3_trans (l2 := [2,1,3])
    . apply Perm3.perm3_swap12
    . apply Perm3.perm3_swap23
  . apply Perm3.perm3_swap12

theorem Perm3_ex1 : Perm3 [1,2,3] [2,3,1] := by
  apply Perm3.perm3_trans (l2 := [2,1,3])
  . apply Perm3.perm3_swap12
  . apply Perm3.perm3_swap23

theorem Perm3_refl : forall (X : Type ) (a b c : X),
  Perm3 [a,b,c] [a,b,c] := by
    intro X a b c
    apply Perm3.perm3_trans (l2 := [b,a,c])
    . apply Perm3.perm3_swap12
    . apply Perm3.perm3_swap12

-- USING EVIDENCE IN PROOFS

open Nat

theorem ev_inversion : forall (n : Nat),
  ev n -> ((n=0)∨ (exists n', n = n'.succ.succ ∧ ev n')) := by
  intro n E
  cases E with
  | ev_0 => simp
  | ev_SS n' E' => right
                   exists n'
