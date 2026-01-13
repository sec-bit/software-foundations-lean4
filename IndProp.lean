import Basics
import Logic

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

-- extra
theorem double_eq_add_self : ∀ n, double n = n + n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [double, ih]
    omega

theorem double_eq_two_mul : ∀ n, double n = 2 * n := by
  intro n
  rw [double_eq_add_self, Nat.two_mul]

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

-- ------------------ ------------------ ------------------ ------------------
-- ------------------ USING EVIDENCE IN PROOFS -----------------------
-- ------------------ ------------------ ------------------ ------------------

open Nat

theorem ev_inversion : forall (n : Nat),
  ev n -> ((n=0)∨ (exists n', n = n'.succ.succ ∧ ev n')) := by
  intro n E
  cases E with
  | ev_0 => simp
  | ev_SS n' E' => right
                   exists n'

theorem evSS_ev : ∀ n, ev (n + 2 ) → ev n := by
  intro n E
  cases E with
  | ev_SS _ E' => exact E'

theorem evSS_ev' : ∀ n, ev (n + 2) → ev n := by
  intro n E
  match E with
  | ev.ev_SS _ E' => exact E'

theorem one_not_even : ¬ ev 1 := by
  intro H
  cases H

theorem one_not_even' : ¬ ev 1 := fun H => nomatch H


theorem SSSSev_even : ∀ n, ev (n + 4) → ev n := by
  intro n H
  cases H with
  | ev_SS _ H' =>
    cases H' with
    | ev_SS _ H'' => exact H''

theorem ev5_nonsense : ev 5 → 2 + 2 = 9 := by
  intro H
  cases H with
  | ev_SS _ H' =>
    cases H' with
    | ev_SS _ H'' => cases H''

-- H'' : ev 1, which is impossible, so `cases H''` closes the goal.

theorem inversion_ex1 : ∀ n m o : Nat, [n, m] = [o, o] → [n] = [m] := by
  intro n m o H
  injection H with h1 h2
  injection h2 with h3
  rw [h1, h3]

theorem inversion_ex2 : ∀ n : Nat, n + 1 = 0 → 2 + 2 = 5 := by
  intro n contra
  contradiction

-- ------------------ INDUCTION ON EVIDENCE ------------------


theorem ev_Even : ∀ n, ev n → Even n := by
  intro n E
  induction E with
  | ev_0 => exact ⟨0, rfl⟩
  | ev_SS n' _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by simp [hk]; omega⟩

theorem ev_Even_iff : ∀ n, ev n ↔ Even n := by
  intro n
  constructor
  · exact ev_Even n
  · intro ⟨k, hk⟩
    rw [hk, <- double_eq_two_mul]
    exact ev_double k

theorem ev_sum : ∀ n m, ev n → ev m → ev (n + m) := by
  intro n m En Em
  induction En with
  | ev_0 => simp; exact Em
  | ev_SS n' _ ih =>
    -- goal: ev (n' + 2 + m)
    have h : n' + 2 + m = (n' + m) + 2 := by omega
    rw [h]
    exact ev.ev_SS (n' + m) ih

theorem ev_ev__ev : ∀ n m, ev (n + m) → ev n → ev m := by
  intro n m E1 E2
  induction E2 with
  | ev_0 => simp at E1; exact E1
  | ev_SS n' _ ih =>
    apply ih
    -- E1 : ev (n' + 2 + m), need ev (n' + m)
    have h : n' + 2 + m = (n' + m) + 2 := by omega
    rw [h] at E1
    cases E1 with
    | ev_SS _ E' => exact E'

theorem ev_plus_plus : ∀ n m p, ev (n + m) → ev (n + p) → ev (m + p) := by
  intro n m p Enm Enp
  apply ev_ev__ev (n + n)
  · have H : ev ((n + m) + (n + p)) := ev_sum _ _ Enm Enp
    have h : (n + m) + (n + p) = (n + n) + (m + p) := by omega
    rw [h] at H
    exact H
  · rw [← double_eq_add_self]
    exact ev_double n

-- ============================================
-- MULTIPLE INDUCTION HYPOTHESES
-- ============================================

inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum (n m : Nat) (Hn : ev' n) (Hm : ev' m) : ev' (n + m)

theorem ev'_ev : ∀ n, ev' n ↔ ev n := by
  intro n
  constructor
  · intro H
    induction H with
    | ev'_0 => exact ev.ev_0
    | ev'_2 => exact ev.ev_SS 0 ev.ev_0
    | ev'_sum n m _ _ ih1 ih2 => exact ev_sum n m ih1 ih2
  · intro H
    induction H with
    | ev_0 => exact ev'.ev'_0
    | ev_SS n _ ih =>
      have h : n + 2 = 2 + n := by omega
      rw [h]
      exact ev'.ev'_sum 2 n ev'.ev'_2 ih

theorem Perm3_symm : ∀ (X : Type) (l1 l2 : List X), Perm3 l1 l2 → Perm3 l2 l1 := by
  intro X l1 l2 E
  induction E with
  | perm3_swap12 a b c => exact Perm3.perm3_swap12 b a c
  | perm3_swap23 a b c => exact Perm3.perm3_swap23 a c b
  | perm3_trans l1 l2 l3 _ _ ih12 ih23 =>
    exact Perm3.perm3_trans l3 l2 l1 ih23 ih12

theorem Perm3_In : ∀ (X : Type) (x : X) (l1 l2 : List X),
    Perm3 l1 l2 → In x l1 → In x l2 := by
  intro X x l1 l2 HPerm HIn
  induction HPerm with
  | perm3_swap12 a b c =>
    simp only [In] at *
    rcases HIn with rfl | rfl | rfl | h
    · right; left; rfl
    · left; rfl
    · right; right; left; rfl
    · exact h.elim
  | perm3_swap23 a b c =>
    simp only [In] at *
    rcases HIn with rfl | rfl | rfl | h
    · left; rfl
    · right; right; left; rfl
    · right; left; rfl
    · exact h.elim
  | perm3_trans _ _ _ _ _ ih1 ih2 =>
    exact ih2 (ih1 HIn)

theorem Perm3_NotIn : ∀ (X : Type) (x : X) (l1 l2 : List X),
    Perm3 l1 l2 → ¬In x l1 → ¬In x l2 := by
  intro X x l1 l2 HPerm HNotIn contra
  apply HNotIn
  exact Perm3_In X x l2 l1 (Perm3_symm X l1 l2 HPerm) contra

example : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  intro contra
  have H : In 3 [1, 2, 4] := Perm3_In Nat 3 _ _ contra (by simp [In])
  simp only [In] at H
  rcases H with h | h | h | h
  · omega
  · omega
  · omega
  · exact h
