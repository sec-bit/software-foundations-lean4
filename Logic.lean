-- Logic.lean
import Tactics

#check (∀ n m : Nat, n + m = m + n )
#check (2=2 : Prop)
#check (3=2 : Prop)
#check (∀ n : Nat, n = 2 : Prop)

def plus_claim : Prop := 2  +2 = 4
#check plus_claim

theorem plus_claim_is_true : plus_claim := by
  rfl

def is_three (n : Nat) : Prop :=
  n = 3

#check is_three

def injective {A B : Type} (f : A -> B) : Prop :=
  ∀ x y : A, f x = f y → x = y

theorem succ_inj : injective Nat.succ := by
  intro x y H
  injection H

#check @Eq

/-
 -------------------- LOGICAL CONNECTIVES -------------------
-/

/- -------------------- CONJUNCTION (Logical AND) ----------------- -/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl

-- Check the constructor for conjunction
#check And.intro -- : ∀ {a b : Prop}, a → b → a ∧ b

-- Alternative: using `And.intro` directly (like Coq's `apply conj`)
example : 3 + 4 = 7 ∧ 2*2=4 := by
  constructor
  .rfl
  .rfl

#check And.intro

example : 3 + 4 = 7 ∧ 2*2=4 := by
  apply And.intro
  .rfl
  .rfl

example (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  intro h
  cases n with
  | zero =>
    constructor
    · rfl
    · simp at h
      exact h
  | succ n' =>
    -- n' + 1 + m = 0 is impossible ( simp at h fails to simplify; revealing contradiction )
    simp at h

theorem plus_is_0 (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  intro h
  cases n with
  | zero =>
    constructor
    · rfl
    · simp at h
      exact h
  | succ n' => simp at h

theorem and_example2 (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro h
  cases h with
  | intro hn hm =>
    rw [hn, hm]

-- Alternative: using angle bracket pattern matching (more concise)
theorem and_example2' (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro ⟨hn, hm⟩
  rw [hn, hm]

-- Alternative: using `obtain` (most idiomatic in Lean 4)
theorem and_example2'' (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro h
  obtain ⟨hn, hm⟩ := h
  rw [hn, hm]

-- You can also have multiple separate hypotheses instead of conjunction
theorem and_example2''' (n m : Nat) : n = 0 → m = 0 → n + m = 0 := by
  intro hn hm
  rw [hn, hm]

-- Using a helper theorem
theorem and_example3 (n m : Nat) : n + m = 0 → n * m = 0 := by
  intro h
  have ⟨hn, hm⟩ := plus_is_0 n m h
  rw [hn]
  rw[hm]

-- Projection theorems (extracting parts of a conjunction)
theorem proj1 (P Q : Prop) : P ∧ Q → P := by
  intro ⟨hp, _⟩
  exact hp

theorem proj2 (P Q : Prop) : P ∧ Q → Q := by
  intro ⟨_, hq⟩
  exact hq

-- Note: Lean has built-in projections And.left and And.right
example (P Q : Prop) : P ∧ Q → P := And.left
example (P Q : Prop) : P ∧ Q → Q := And.right

-- Conjunction is commutative
theorem and_commut (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  constructor
  · exact hq
  · exact hp

-- Conjunction is associative
theorem and_assoc' (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro ⟨hp, hq, hr⟩
  constructor
  · constructor
    · exact hp
    · exact hq
  · exact hr

-- Check the type of And
#check And -- : Prop → Prop → Prop


/- ---------------------- DISJUNCTION (Logical OR) -------------------  -/
#check Or -- Prop → Prop → Prop

-- Using a disjunction: case analysis
theorem factor_is_0 (n m : Nat) : n = 0 ∨ m = 0 → n * m = 0 := by
  intro h
  cases h with
  | inl hn => rw [hn]; simp
  | inr hm => rw [hm]; simp

-- Introducing a disjunction: left side
theorem or_intro_l (A B : Prop) : A → A ∨ B := by
  intro ha
  left
  exact ha

-- Alternative: using Or.inl directly
theorem or_intro_l' (A B : Prop) : A → A ∨ B :=
  Or.inl

-- Pattern matching in intro
theorem zero_or_succ (n : Nat) : n = 0 ∨ n = .succ (.pred n) := by
  cases n with
  | zero =>
    left
    rfl
  | succ n' =>
    right
    rfl

-- Reverse direction
theorem mult_is_0 (n m : Nat) : n * m = 0 → n = 0 ∨ m = 0 := by
  intro h
  cases n with
  | zero =>
    left
    rfl
  | succ n' =>
    cases m with
    | zero =>
      right
      rfl
    | succ m' => contradiction

-- Or is commutative
theorem or_commut (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

-- Alternative: more concise with pattern matching
theorem or_commut' (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

/- -------------  FALSEHOOD AND NEGATION -------------- -/

-- Negation is implication to False
#check Not -- Prop → Prop
#check (¬ (2 = 3)) -- Prop

-- From falsehood, anything follows (ex falso quodlibet)
theorem ex_falso_quodlibet (P : Prop) : False → P := by
  intro contra
  contradiction

-- Alternative: explicit eliminator
theorem ex_falso_quodlibet' (P : Prop) : False → P :=
  False.elim

-- Negation implies anything from the proposition
theorem not_implies_our_not (P : Prop) : ¬P → (∀ (Q : Prop), P → Q) := by
  intro hnotP Q hp
  -- ¬P means P → False
  have : False := hnotP hp
  contradiction

-- Not equal notation
example : 0 ≠ 1 := by
  intro h
  -- 0 = 1 is contradictory
  contradiction

-- Alternative proof
theorem zero_not_one : 0 ≠ 1 := by
  -- unfold Not -- not needed in Lean 4, ¬ is transparent
  intro h
  simp at h -- simplifies to False

-- ¬False is provable
theorem not_False : ¬False := by
  intro h
  exact h

-- Alternative: using id function
theorem not_False' : ¬False := id

-- Contradiction implies anything
theorem contradiction_implies_anything (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro ⟨hp, hnp⟩
  -- ¬P means P → False
  have : False := hnp hp
  contradiction

-- Double negation introduction
theorem double_neg ( P : Prop) : P → ¬¬P := by
  intro h hnp
  exact hnp h

-- Contrapositive
theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hpq hnq hp
  have hq := hpq hp
  exact hnq hq

-- Can't have both P and ¬P
theorem not_both_true_and_false (P : Prop) : ¬(P ∧ ¬P) := by
  intro ⟨hp, hnp⟩
  exact hnp hp

-- De Morgan's law
theorem de_morgan_not_or (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  · intro hp
    apply h
    left
    exact hp
  · intro hq
    apply h
    right
    exact hq

-- Negating a universal quantifier
theorem not_S_pred_n : ¬(∀ n : Nat, Nat.succ (Nat.pred n) = n) := by
  intro h
  have : Nat.succ (Nat.pred 0) = 0 := h 0
  simp at this

-- Bool: not true implies false
theorem not_true_is_false (b : Bool) : b ≠ true → b = false := by
  intro h
  cases b with
  | false => rfl
  | true =>
    exfalso
    apply h
    rfl

-- Alternative: more concise
theorem not_true_is_false' (b : Bool) : b ≠ true → b = false := by
  intro h
  cases b with
  | false => rfl
  | true => contradiction
