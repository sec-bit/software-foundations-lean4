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


-- ------------------ USING EVIDENCE IN PROOFS -----------------------


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


-- ------------------------ MULTIPLE INDUCTION HYPOTHESES -----------------------


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

-- ---------------------------- EXERCISING WITH INDUCTIVE RELATIONS ----------------------------

namespace Playground

inductive Le : Nat → Nat → Prop where
  | le_n (n : Nat) : Le n n
  | le_S (n m : Nat) (H : Le n m) : Le n (m + 1)

def Lt (n m : Nat) := Le (n + 1) m
def Ge (m n : Nat) := Le n m

end Playground

open Playground.Le
open Playground (Le Lt Ge)

theorem test_le1 : Le 3 3 := le_n 3

theorem test_le2 : Le 3 6 := le_S 3 5 (le_S 3 4 (le_S 3 3 (le_n 3)))

theorem test_le3 : Le 2 1 → 2 + 2 = 5 := by
  intro H
  contradiction

theorem Le_trans : ∀ m n o, Le m n → Le n o → Le m o := by
  intro m n o Emn Eno
  induction Eno with
  | le_n => exact Emn
  | le_S o' _ ih => exact le_S m o' ih

theorem O_Le_n : ∀ n, Le 0 n := by
  intro n
  induction n with
  | zero => exact le_n 0
  | succ n' ih => exact le_S 0 n' ih

theorem n_Le_m__Sn_Le_Sm : ∀ n m, Le n m → Le (n + 1) (m + 1) := by
  intro n m H
  induction H with
  | le_n => exact le_n (n + 1)
  | le_S m' _ ih => exact le_S (n + 1) (m' + 1) ih

theorem Sn_Le_Sm__n_Le_m : ∀ n m, Le (n + 1) (m + 1) → Le n m := by
  intro n m H
  cases H with
  | le_n => exact le_n n
  | le_S m' H' =>
    apply Le_trans n (n + 1) m
    · exact le_S n n (le_n n)
    · exact H'


theorem Le_plus_l : ∀ a b, Le a (a + b) := by
  intro a b
  induction b with
  | zero => simp; exact le_n a
  | succ b' ih =>
    have h : a + (b' + 1) = (a + b') + 1 := by omega
    rw [h]
    exact le_S a (a + b') ih

theorem plus_Le : ∀ n1 n2 m, Le (n1 + n2) m → Le n1 m ∧ Le n2 m := by
  intro n1 n2 m H
  constructor
  · exact Le_trans n1 (n1 + n2) m (Le_plus_l n1 n2) H
  · have h : Le n2 (n2 + n1) := Le_plus_l n2 n1
    have h2 : n2 + n1 = n1 + n2 := by omega
    rw [h2] at h
    exact Le_trans n2 (n1 + n2) m h H

theorem plus_Le_cases : ∀ n m p q, Le (n + m) (p + q) → Le n p ∨ Le m q := by
  intro n
  induction n with
  | zero => intros; left; exact O_Le_n _
  | succ n' ih =>
    intro m p q H
    cases p with
    | zero =>
      right
      have ⟨_, h2⟩ := plus_Le (n' + 1) m (0 + q) H
      simp at h2
      exact h2
    | succ p' =>
      have h : (n' + 1) + m = n' + (m + 1) := by omega
      have h2 : (p' + 1) + q = p' + (q + 1) := by omega
      rw [h, h2] at H
      cases ih (m + 1) p' (q + 1) H with
      | inl hl => left; exact n_Le_m__Sn_Le_Sm n' p' hl
      | inr hr => right; exact Sn_Le_Sm__n_Le_m m q hr

theorem plus_Le_compat_l : ∀ n m p, Le n m → Le (p + n) (p + m) := by
  intro n m p H
  induction p with
  | zero => simp; exact H
  | succ p' ih =>
    have h1 : (p' + 1) + n = (p' + n) + 1 := by omega
    have h2 : (p' + 1) + m = (p' + m) + 1 := by omega
    rw [h1, h2]
    exact n_Le_m__Sn_Le_Sm (p' + n) (p' + m) ih

theorem plus_Le_compat_r : ∀ n m p, Le n m → Le (n + p) (m + p) := by
  intro n m p H
  have h1 : n + p = p + n := by omega
  have h2 : m + p = p + m := by omega
  rw [h1, h2]
  exact plus_Le_compat_l n m p H

theorem Le_plus_trans : ∀ n m p, Le n m → Le n (m + p) := by
  intro n m p H
  induction p with
  | zero => simp; exact H
  | succ p' ih =>
    have h : m + (p' + 1) = (m + p') + 1 := by omega
    rw [h]
    exact le_S n (m + p') ih

theorem Lt_Ge_cases : ∀ n m, Lt n m ∨ Ge n m := by
  intro n m
  cases m with
  | zero => right; unfold Ge; exact O_Le_n n
  | succ m' =>
    induction n with
    | zero => left; unfold Lt; exact n_Le_m__Sn_Le_Sm 0 m' (O_Le_n m')
    | succ n' ih =>
      cases ih with
      | inl hl =>
        unfold Lt at hl
        cases hl with
        | le_n => right; unfold Ge; exact le_n _
        | le_S k H => left; unfold Lt; exact n_Le_m__Sn_Le_Sm _ _ H
      | inr hr =>
        unfold Ge at hr
        right; unfold Ge; exact le_S _ _ hr

theorem n_Lt_m__n_Le_m : ∀ n m, Lt n m → Le n m := by
  intro n m H
  unfold Lt at H
  exact Le_trans n (n + 1) m (le_S n n (le_n n)) H

theorem plus_Lt : ∀ n1 n2 m, Lt (n1 + n2) m → Lt n1 m ∧ Lt n2 m := by
  intro n1 n2 m H
  unfold Lt at *
  constructor
  · apply Le_trans (n1 + 1) ((n1 + n2) + 1) m
    · exact n_Le_m__Sn_Le_Sm n1 (n1 + n2) (Le_plus_l n1 n2)
    · exact H
  · apply Le_trans (n2 + 1) ((n1 + n2) + 1) m
    · have h : Le n2 (n1 + n2) := by
        have h' : n2 + n1 = n1 + n2 := by omega
        rw [← h']; exact Le_plus_l n2 n1
      exact n_Le_m__Sn_Le_Sm n2 (n1 + n2) h
    · exact H

theorem leb_complete : ∀ n m, Nat.ble n m = true → Le n m := by
  intro n m
  induction n generalizing m with
  | zero => intro _; exact O_Le_n m
  | succ n' ih =>
    intro H
    cases m with
    | zero => contradiction
    | succ m' =>
      apply n_Le_m__Sn_Le_Sm
      apply ih
      exact H

theorem leb_correct : ∀ n m, Le n m → Nat.ble n m = true := by
  intro n m H
  induction H with
  | le_n =>
    induction n with
    | zero => rfl
    | succ n' ih => simp [Nat.ble]
  | le_S m _ ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      simp [Nat.ble] at ih ⊢
      cases m with
      | zero => simp at ih
      | succ m' => simp at ih ⊢; omega

theorem leb_iff : ∀ n m, Nat.ble n m = true ↔ Le n m := by
  intro n m
  constructor
  · exact leb_complete n m
  · exact leb_correct n m

theorem leb_true_trans : ∀ n m o,
    Nat.ble n m = true → Nat.ble m o = true → Nat.ble n o = true := by
  intro n m o Hnm Hmo
  apply leb_correct
  apply Le_trans n m o
  · exact leb_complete n m Hnm
  · exact leb_complete m o Hmo

namespace R

inductive R : Nat → Nat → Nat → Prop where
  | c1 : R 0 0 0
  | c2 (m n o : Nat) (H : R m n o) : R (m + 1) n (o + 1)
  | c3 (m n o : Nat) (H : R m n o) : R m (n + 1) (o + 1)
  | c4 (m n o : Nat) (H : R (m + 1) (n + 1) (o + 2)) : R m n o
  | c5 (m n o : Nat) (H : R m n o) : R n m o

def fR : Nat → Nat → Nat := Nat.add

open R

theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o := by
  intro m n o
  constructor
  · intro H
    induction H with
    | c1 => rfl
    | c2 m n o _ ih => simp [fR] at *; omega
    | c3 m n o _ ih => simp [fR] at *; omega
    | c4 m n o _ ih => simp [fR] at *; omega
    | c5 m n o _ ih => simp [fR] at *; omega
  · intro H
    induction m generalizing n o with
    | zero =>
      simp [fR] at H
      subst H
      induction n with
      | zero => exact c1
      | succ n' ih => exact c3 0 n' n' ih
    | succ m' ih =>
      simp [fR] at H
      subst H
      have h : m' + 1 + n = (m' + n) + 1 := by omega
      rw [h]
      exact c2 m' n (m' + n) (ih n (m' + n) rfl)

end R

inductive Subseq : List Nat → List Nat → Prop where
  | nil (l : List Nat) : Subseq [] l
  | cons_both (x : Nat) (l1 l2 : List Nat) (H : Subseq l1 l2) : Subseq (x :: l1) (x :: l2)
  | cons_right (x : Nat) (l1 l2 : List Nat) (H : Subseq l1 l2) : Subseq l1 (x :: l2)

open Subseq

theorem Subseq_refl : ∀ l : List Nat, Subseq l l := by
  intro l
  induction l with
  | nil => exact nil []
  | cons x l' ih => exact cons_both x l' l' ih

theorem Subseq_app : ∀ l1 l2 l3 : List Nat, Subseq l1 l2 → Subseq l1 (l2 ++ l3) := by
  intro l1 l2 l3 H
  induction H with
  | nil _ => exact nil _
  | cons_both x l1 l2 _ ih => exact cons_both x l1 (l2 ++ l3) ih
  | cons_right x l1 l2 _ ih => exact cons_right x l1 (l2 ++ l3) ih

theorem Subseq_trans : ∀ l1 l2 l3 : List Nat,
    Subseq l1 l2 → Subseq l2 l3 → Subseq l1 l3 := by
  intro l1 l2 l3 H12 H23
  induction H23 generalizing l1 with
  | nil _ =>
    cases H12 with
    | nil _ => exact nil _
  | cons_both x l2 l3 _ ih =>
    cases H12 with
    | nil _ => exact nil _
    | cons_both _ l1' _ H12' => exact cons_both x l1' l3 (ih l1' H12')
    | cons_right _ l1 _ H12' => exact cons_right x l1 l3 (ih l1 H12')
  | cons_right x l2 l3 _ ih => exact cons_right x l1 l3 (ih l1 H12)

inductive TotalRelation : Nat → Nat → Prop where
  | total_rel (n m : Nat) : TotalRelation n m

theorem total_relation_is_total : ∀ n m, TotalRelation n m :=
  fun n m => TotalRelation.total_rel n m

inductive EmptyRelation : Nat → Nat → Prop where

theorem empty_relation_is_empty : ∀ n m, ¬ EmptyRelation n m := by
  intro n m H
  cases H



-- ---------------------------- CASE STUDY: REGULAR EXPRESSIONS ----------------------------

-- Regular expression syntax
inductive reg_exp (T : Type) : Type where
  | EmptySet : reg_exp T
  | EmptyStr : reg_exp T
  | Char : T → reg_exp T
  | App : reg_exp T → reg_exp T → reg_exp T
  | Union : reg_exp T → reg_exp T → reg_exp T
  | Star : reg_exp T → reg_exp T

open reg_exp

-- Matching relation
inductive exp_match {T : Type} : List T → reg_exp T → Prop where
  | MEmpty : exp_match [] EmptyStr
  | MChar (x : T) : exp_match [x] (Char x)
  | MApp (s1 : List T) (re1 : reg_exp T) (s2 : List T) (re2 : reg_exp T)
         (H1 : exp_match s1 re1) (H2 : exp_match s2 re2) :
         exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL (s1 : List T) (re1 re2 : reg_exp T)
            (H1 : exp_match s1 re1) :
            exp_match s1 (Union re1 re2)
  | MUnionR (s2 : List T) (re1 re2 : reg_exp T)
            (H2 : exp_match s2 re2) :
            exp_match s2 (Union re1 re2)
  | MStar0 (re : reg_exp T) : exp_match [] (Star re)
  | MStarApp (s1 s2 : List T) (re : reg_exp T)
             (H1 : exp_match s1 re) (H2 : exp_match s2 (Star re)) :
             exp_match (s1 ++ s2) (Star re)

-- Notation (can't use =~ easily in Lean, using infix)
infix:50 " =~ " => exp_match

open exp_match

-- Examples
example : [1] =~ Char 1 := MChar 1

example : [1, 2] =~ App (Char 1) (Char 2) := by
  have h : [1, 2] = [1] ++ [2] := rfl
  rw [h]
  exact MApp [1] (Char 1) [2] (Char 2) (MChar 1) (MChar 2)

theorem Char_match : ∀ {T} {s : List T} {x: T}, s =~ Char x → s = [x] := by
  intro T s x H
  cases H
  rfl

example : ¬([1, 2] =~ Char 1) := by
  intro H
  have h := Char_match H
  simp at h

-- Convert list to regex that matches exactly that list
def reg_exp_of_list {T : Type} (l : List T) : reg_exp T :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] := by
  simp [reg_exp_of_list]
  have h1 : [1, 2, 3] = [1] ++ [2, 3] := rfl
  rw [h1]
  apply MApp
  · exact MChar 1
  · have h2 : [2, 3] = [2] ++ [3] := rfl
    rw [h2]
    apply MApp
    · exact MChar 2
    · have h3 : [3] = [3] ++ [] := rfl
      rw [h3]
      apply MApp
      · exact MChar 3
      · exact MEmpty

theorem MStar1 : ∀ T (s : List T) (re : reg_exp T),
    s =~ re → s =~ Star re := by
  intro T s re H
  have h : s = s ++ [] := by simp
  rw [h]
  exact MStarApp s [] re H (MStar0 re)

theorem EmptySet_is_empty : ∀ T (s : List T), ¬(s =~ EmptySet) := by
  intro T s H
  cases H

theorem MUnion' : ∀ T (s : List T) (re1 re2 : reg_exp T),
    s =~ re1 ∨ s =~ re2 → s =~ Union re1 re2 := by
  intro T s re1 re2 H
  cases H with
  | inl h => exact MUnionL s re1 re2 h
  | inr h => exact MUnionR s re1 re2 h

-- fold for lists
def fold {X Y : Type} (f : X → Y → Y) (l : List X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

theorem MStar' : ∀ T (ss : List (List T)) (re : reg_exp T),
    (∀ s, In s ss → s =~ re) →
    fold (· ++ ·) ss [] =~ Star re := by
  intro T ss re H
  induction ss with
  | nil => simp [fold]; exact MStar0 re
  | cons s1 ss' ih =>
    simp [fold]
    apply MStarApp
    · apply H; simp [In]
    · apply ih; intro s hs; apply H; simp [In]; right; exact hs

def EmptyStr' {T : Type} : reg_exp T := Star EmptySet

-- Helper for EmptyStr
theorem EmptyStr_match : ∀ {T} {s : List T}, s =~ EmptyStr → s = [] := by
  intro T s H
  cases H
  rfl

-- Characters in a regex
def re_chars {T : Type} (re : reg_exp T) : List T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | reg_exp.Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | reg_exp.Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re

theorem in_re_match : ∀ T (s : List T) (re : reg_exp T) (x : T),
    s =~ re → In x s → In x (re_chars re) := by
  intro T s re x HMatch HIn
  induction HMatch with
  | MEmpty => simp [In] at HIn
  | MChar x' => simp [re_chars]; exact HIn
  | MApp s1 re1 s2 re2 _ _ ih1 ih2 =>
    simp [re_chars]
    rw [In_app_iff] at HIn
    rw [In_app_iff]
    cases HIn with
    | inl h => left; exact ih1 h
    | inr h => right; exact ih2 h
  | MUnionL s1 re1 re2 _ ih =>
    simp [re_chars]
    rw [In_app_iff]
    left; exact ih HIn
  | MUnionR s2 re1 re2 _ ih =>
    simp [re_chars]
    rw [In_app_iff]
    right; exact ih HIn
  | MStar0 _ => simp [In] at HIn
  | MStarApp s1 s2 re _ _ ih1 ih2 =>
    simp [re_chars]
    rw [In_app_iff] at HIn
    cases HIn with
    | inl h => exact ih1 h
    | inr h => exact ih2 h

-- Check if regex can match some string
def re_not_empty {T : Type} (re : reg_exp T) : Bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | reg_exp.Char _ => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | reg_exp.Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star _ => true

theorem re_not_empty_correct : ∀ T (re : reg_exp T),
    (∃ s, s =~ re) ↔ re_not_empty re = true := by
  intro T re
  constructor
  · intro ⟨s, HMatch⟩
    induction HMatch with
    | MEmpty => rfl
    | MChar _ => rfl
    | MApp _ _ _ _ _ _ ih1 ih2 =>
      simp [re_not_empty]; constructor; exact ih1; exact ih2
    | MUnionL _ _ _ _ ih => simp [re_not_empty]; left; exact ih
    | MUnionR _ _ _ _ ih => simp [re_not_empty]; right; exact ih
    | MStar0 _ => rfl
    | MStarApp _ _ _ _ _ _ _ => rfl
  · intro H
    induction re with
    | EmptySet => simp [re_not_empty] at H
    | EmptyStr => exact ⟨[], MEmpty⟩
    | Char t => exact ⟨[t], MChar t⟩
    | App re1 re2 ih1 ih2 =>
      simp [re_not_empty] at H
      obtain ⟨h1, h2⟩ := H
      obtain ⟨s1, hs1⟩ := ih1 h1
      obtain ⟨s2, hs2⟩ := ih2 h2
      exact ⟨s1 ++ s2, MApp s1 re1 s2 re2 hs1 hs2⟩
    | Union re1 re2 ih1 ih2 =>
      simp [re_not_empty] at H
      cases H with
      | inl h =>
        obtain ⟨s1, hs1⟩ := ih1 h
        exact ⟨s1, MUnionL s1 re1 re2 hs1⟩
      | inr h =>
        obtain ⟨s2, hs2⟩ := ih2 h
        exact ⟨s2, MUnionR s2 re1 re2 hs2⟩
    | Star _ _ => exact ⟨[], MStar0 _⟩

-- star_app: Key lemma requiring "remember" pattern
-- lean doesn't have remember tactic
-- In Lean, we use `generalize` or carry the equality through manually

-- star_app with explicit equality argument (avoids generalize issues)
theorem star_app_aux : ∀ T (s1 s2 : List T) (re re' : reg_exp T),
    re' = Star re →
    s1 =~ re' →
    s2 =~ Star re →
    s1 ++ s2 =~ Star re := by
  intro T s1 s2 re re' heq H1 H2
  induction H1 generalizing re with
  | MEmpty => simp at heq
  | MChar _ => simp  at heq
  | MApp _ _ _ _ _ _ _ _ => simp at heq
  | MUnionL _ _ _ _ _ => simp at heq
  | MUnionR _ _ _ _ _ => simp  at heq
  | MStar0 re'' =>
    simp at heq
    subst heq
    simp
    exact H2
  | MStarApp s1' s2' re'' _ _ _ ih2 =>
    simp at heq
    subst heq
    rw [List.append_assoc]
    apply MStarApp
    · assumption
    · exact ih2 _ rfl H2

theorem star_app : ∀ T (s1 s2 : List T) (re : reg_exp T),
    s1 =~ Star re →
    s2 =~ Star re →
    s1 ++ s2 =~ Star re := by
  intro T s1 s2 re H1 H2
  exact star_app_aux T s1 s2 re (Star re) rfl H1 H2

theorem MStar'' : ∀ T (s : List T) (re : reg_exp T),
    s =~ Star re →
    ∃ ss : List (List T),
      s = fold (· ++ ·) ss [] ∧ ∀ s', In s' ss → s' =~ re := by
  intro T s re HMatch
  generalize hre : Star re = re' at HMatch
  induction HMatch with
  | MEmpty => injection hre
  | MChar _ => injection hre
  | MApp _ _ _ _ _ _ _ _ => injection hre
  | MUnionL _ _ _ _ _ => injection hre
  | MUnionR _ _ _ _ _ => injection hre
  | MStar0 _ =>
    exact ⟨[], by simp [fold], by intro s' h; simp [In] at h⟩
  | MStarApp s1 s2 re' H1 _ _ ih2 =>
    injection hre with hre'
    subst hre'
    obtain ⟨ss', hss'_eq, hss'_match⟩ := ih2 rfl
    exact ⟨s1 :: ss',
           by simp [fold]; rw [hss'_eq],
           by intro s' hs'
              simp [In] at hs'
              cases hs' with
              | inl h => subst h; exact H1
              | inr h => exact hss'_match s' h⟩



-- ----------------------- CASE STUDY : IMPROVING REFLECTION ----------------


-- Re-prove this locally to avoid namespace/import clashes
theorem eqb_iff_eq (n m : Nat) : eqb n m = true ↔ n = m := by
  induction n generalizing m with
  | zero =>
    cases m <;> simp [eqb]
  | succ n' ih =>
    cases m with
    | zero => simp [eqb]
    | succ m' =>
      simp [eqb]
      exact ih m'

-- 2. First filter theorem (using Prop-based In)
theorem filter_not_empty_In (n : Nat) (l : List Nat) :
  (l.filter (fun x => eqb n x)) ≠ [] → In n l := by
  induction l with
  | nil =>
    intro h
    contradiction
  | cons m l' ih =>
    dsimp [List.filter]
    cases h : eqb n m
    · -- case false
      intro h_neq
      right
      apply ih
      exact h_neq
    · -- case true
      intro _
      rw[eqb_iff_eq] at h
      rw [h]
      left
      rfl

-- 3. The Custom Reflect Type
inductive Reflect (P : Prop) : Bool → Prop where
  | ReflectT (h : P) : Reflect P true
  | ReflectF (h : ¬P) : Reflect P false

theorem iff_reflect (P : Prop) (b : Bool) : (P ↔ b = true) → Reflect P b := by
  intro h
  cases b
  · -- case false
    apply Reflect.ReflectF
    -- 'rw [h]'
    simp [h]
  · -- case true
    apply Reflect.ReflectT
    simp [h]

theorem reflect_iff (P : Prop) (b : Bool) : Reflect P b → (P ↔ b = true) := by
  intro h
  cases h with
  | ReflectT hp =>
    constructor
    · intro _; rfl
    · intro _; exact hp
  | ReflectF hnp =>
    constructor
    · intro hp; contradiction
    · intro htrue; contradiction

-- 4. Using Reflect for eqb
theorem eqbP (n m : Nat) : Reflect (n = m) (eqb n m) := by
  apply iff_reflect
  rw [eqb_iff_eq]

theorem filter_not_empty_In' (n : Nat) (l : List Nat) :
  (l.filter (fun x => eqb n x)) ≠ [] → In n l := by
  induction l with
  | nil =>
    intro h
    contradiction
  | cons m l' ih =>
    dsimp [List.filter]
    cases h : eqb n m
    · -- Case: eqb n m = false
      intro h_neq
      right
      apply ih
      exact h_neq
    · -- Case: eqb n m = true
      intro _
      have H := eqbP n m   -- H : Reflect (n=m) (eqb n m)
      rw [h] at H          -- H : Reflect (n=m) true
      cases H              -- Now 'cases' works perfectly
      case ReflectT EQnm => -- EQnm : n = m
        rw [EQnm]
        left
        rfl

-- 5. Counting and Practice
def count (n : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | m :: l' => (if eqb n m then 1 else 0) + count n l'

theorem eqbP_practice (n : Nat) (l : List Nat) :
  count n l = 0 → ¬(In n l) := by
  intro h_count
  induction l with
  | nil =>
    intro h_in
    contradiction
  | cons m l' ih =>
    dsimp [count] at h_count
    -- FIX: Split on the boolean first
    cases h : eqb n m
    · -- Case: eqb n m = false
      -- The 'if' simplifies to 0
      simp [h] at h_count
      intro h_in
      cases h_in with
      | inl Hhead =>
        have H := eqbP n m
        rw [h] at H         -- H : Reflect (n=m) false
        cases H             -- Unpack it
        case ReflectF Hneq => -- Hneq : n ≠ m
          rw [Hhead] at Hneq
          contradiction
      | inr Htail =>
        apply ih
        exact h_count
        exact Htail
    · simp [h] at h_count
