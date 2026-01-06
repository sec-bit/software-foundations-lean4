-- Logic.lean

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
  LOGICAL CONNECTIVES
-/

/-
  CONJUNCTION (Logical AND)

  In Lean, conjunction is written with ∧ (type \and or use /\)
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl

-- Check the constructor for conjunction
#check And.intro -- : ∀ {a b : Prop}, a → b → a ∧ b

-- Alternative: using `And.intro` directly (like Coq's `apply conj`)
example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl
  · rfl

-- Another alternative: anonymous constructor syntax
example : 3 + 4 = 7 ∧ 2 * 2 = 4 :=
  ⟨by rfl, by rfl⟩

example (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  intro h
  cases n with
  | zero =>
    constructor
    · rfl
    · exact h
  | succ n' =>
    -- n' + 1 + m = 0 is impossible
    contradiction

-- Destructing a conjunction hypothesis
theorem and_example2 (n m : Nat) : n = 0 ∧ m = 0 → n + m = 0 := by
  intro h
  cases h with
  | intro hn hm =>
    rw [hn, hm]
    rfl

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
theorem plus_is_0 (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  intro h
  cases n with
  | zero =>
    constructor
    · rfl
    · exact h
  | succ n' => contradiction

theorem and_example3 (n m : Nat) : n + m = 0 → n * m = 0 := by
  intro h
  have ⟨hn, hm⟩ := plus_is_0 n m h
  rw [hn]

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
theorem and_assoc (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro ⟨hp, hq, hr⟩
  constructor
  · constructor
    · exact hp
    · exact hq
  · exact hr

-- Check the type of And
#check And -- : Prop → Prop → Prop
