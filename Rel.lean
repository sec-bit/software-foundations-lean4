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

-- -------------------- EQUIVALENCE, ORDER, PREORDER --------------------

def equivalence {α : Type} (R : relation α) : Prop :=
  reflexive R ∧ symmetric R ∧ transitive R

def order {α : Type} (R : relation α) : Prop :=
  reflexive R ∧ antisymmetric R ∧ transitive R

def preorder {α : Type} (R : relation α) : Prop :=
  reflexive R ∧ transitive R

theorem le_order : order Le := by
  unfold order
  exact ⟨le_reflexive, le_antisymmetric, le_trans⟩

-- -------------------- REFLEXIVE TRANSITIVE CLOSURE --------------------

inductive clos_refl_trans {α : Type} (R : relation α) : relation α where
  | rt_step (x y : α) : R x y → clos_refl_trans R x y
  | rt_refl (x : α) : clos_refl_trans R x x
  | rt_trans (x y z : α) : clos_refl_trans R x y → clos_refl_trans R y z → clos_refl_trans R x z

open clos_refl_trans

theorem next_nat_closure_is_le : ∀ n m, Le n m ↔ clos_refl_trans next_nat n m := by
  intro n m
  constructor
  -- → direction
  · intro h
    induction h with
    | refl => exact rt_refl n
    | step _ ih => exact rt_trans n _ _ ih (rt_step _ _ next_nat.nn)
  -- ← direction
  · intro h
    induction h with
    | rt_step x y hr =>
      cases hr
      exact Le.step Le.refl
    | rt_refl x => exact Le.refl
    | rt_trans x y z _ _ ih1 ih2 => exact le_trans x y z ih1 ih2
-- -------------------- LEFT-UNARY CLOSURE --------------------

inductive clos_refl_trans_1n {α : Type} (R : relation α) : α → α → Prop where
  | rt1n_refl (x : α) : clos_refl_trans_1n R x x
  | rt1n_trans (x y z : α) : R x y → clos_refl_trans_1n R y z → clos_refl_trans_1n R x z

theorem rsc_R {α : Type} (R : relation α) (x y : α) :
    R x y → clos_refl_trans_1n R x y := by
  intro h
  exact clos_refl_trans_1n.rt1n_trans x y y h (clos_refl_trans_1n.rt1n_refl y)

theorem rsc_trans {α : Type} (R : relation α) (x y z : α) :
    clos_refl_trans_1n R x y →
    clos_refl_trans_1n R y z →
    clos_refl_trans_1n R x z := by
  intro h1 h2
  induction h1 with
  | rt1n_refl _ => exact h2
  | rt1n_trans _ y' _ hxy _ ih => exact clos_refl_trans_1n.rt1n_trans _ y' _ hxy (ih h2)

theorem rtc_rsc_coincide {α : Type} (R : relation α) (x y : α) :
    clos_refl_trans R x y ↔ clos_refl_trans_1n R x y := by
  constructor
  · intro h
    induction h with
    | rt_step x y hr => exact rsc_R R x y hr
    | rt_refl x => exact clos_refl_trans_1n.rt1n_refl x
    | rt_trans x y z _ _ ih1 ih2 => exact rsc_trans R x y z ih1 ih2
  · intro h
    induction h with
    | rt1n_refl x => exact rt_refl x
    | rt1n_trans x y z hxy _ ih => exact rt_trans x y z (rt_step x y hxy) ih
