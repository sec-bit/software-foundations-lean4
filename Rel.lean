-- Rel.lean
-- Properties of Relations

-- -------------------- RELATIONS --------------------

def relation (α : Type) := α → α → Prop

-- Our own Le (not Nat.le)
inductive Le : Nat → Nat → Prop where
  | refl : Le n n
  | step : Le n m → Le n (m + 1)

#check (Le : Nat → Nat → Prop)
#check (Le : relation Nat)

-- -------------------- PARTIAL FUNCTIONS --------------------

def partial_function {α : Type} (R : relation α) : Prop :=
  ∀ x y1 y2, R x y1 → R x y2 → y1 = y2

inductive next_nat : Nat → Nat → Prop where
  | nn : next_nat n (n + 1)

#check (next_nat : relation Nat)

theorem next_nat_partial_function : partial_function next_nat := by
  unfold partial_function
  intro x y1 y2 h1 h2
  cases h1
  cases h2
  rfl

theorem le_not_a_partial_function : ¬ partial_function Le := by
  unfold partial_function
  intro hc
  have nonsense : 0 = 1 := hc 0 0 1 Le.refl (Le.step Le.refl)
  contradiction

inductive total_relation : Nat → Nat → Prop where
  | total : total_relation n m

theorem total_relation_not_partial_function : ¬ partial_function total_relation := by
  intro hc
  have nonsense : 0 = 1 := hc 1 0 1 total_relation.total total_relation.total
  contradiction

inductive empty_relation : Nat → Nat → Prop where

theorem empty_relation_partial_function : partial_function empty_relation := by
  intro x y1 y2 h
  cases h

-- -------------------- REFLEXIVE RELATIONS --------------------

def reflexive {α : Type} (R : relation α) : Prop :=
  ∀ a, R a a

theorem le_reflexive : reflexive Le := by
  intro n
  exact Le.refl

-- -------------------- TRANSITIVE RELATIONS --------------------

def transitive {α : Type} (R : relation α) : Prop :=
  ∀ a b c, R a b → R b c → R a c

theorem le_trans : transitive Le := by
  intro n m o hnm hmo
  induction hmo with
  | refl => exact hnm
  | step _ ih => exact Le.step ih

-- -------------------- HELPER LEMMAS --------------------

theorem le_Sn_le : Le (n + 1) m → Le n m := by
  intro h
  have step : Le n (n + 1) := Le.step Le.refl
  exact le_trans n (n + 1) m step h

theorem le_S_n : Le (n + 1) (m + 1) → Le n m := by
  intro h
  cases h with
  | refl => exact Le.refl
  | step h' => exact le_Sn_le h'

theorem le_Sn_n : ¬ Le (n + 1) n := by
  intro h
  induction n with
  | zero => cases h
  | succ n ih => exact ih (le_S_n h)

-- -------------------- SYMMETRIC RELATIONS --------------------

def symmetric {α : Type} (R : relation α) : Prop :=
  ∀ a b, R a b → R b a

theorem le_not_symmetric : ¬ symmetric Le := by
  intro h
  have nonsense : Le 1 0 := h 0 1 (Le.step Le.refl)
  cases nonsense

-- -------------------- ANTISYMMETRIC RELATIONS --------------------

def antisymmetric {α : Type} (R : relation α) : Prop :=
  ∀ a b, R a b → R b a → a = b

theorem le_antisymmetric : antisymmetric Le := by
  intro a b h1 h2
  cases h1 with
  | refl => rfl
  | step h =>
    exfalso
    exact le_Sn_n (le_trans _ a _ h2 h)
