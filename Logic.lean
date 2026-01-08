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


/- --------------------  TRUTH -------------------- -/

-- True is proven by trivial or True.intro
theorem True_is_true : True := trivial

-- Alternative
theorem True_is_true' : True := True.intro

-- Using True in pattern matching (like Coq's discriminate)
def disc_fn (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

-- Discriminating using True/False pattern
theorem disc_example (n : Nat) : ¬(0 = n.succ) := by
  intro contra
  have h : disc_fn 0 := trivial
  rw [contra] at h
  -- h is now False
  exact h

-- List version
theorem nil_is_not_cons {X : Type} (x : X) (xs : List X) : ¬([] = x :: xs) := by
  intro contra
  have h : (match @List.nil X with
            | [] => True
            | _ :: _ => False) := trivial
  rw [contra] at h
  exact h


/- --------------------  LOGICAL EQUIVALENCE -------------------- -/

#check Iff -- Prop → Prop → Prop

-- Iff is symmetric
theorem iff_sym (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨hab, hba⟩
  constructor
  · exact hba
  · exact hab

-- Using the iff we proved earlier
theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · exact not_true_is_false b
  · intro h
    rw [h]
    intro h'
    contradiction

-- Applying iff in forward direction
theorem apply_iff_example1 (P Q R : Prop) : (P ↔ Q) → (Q → R) → (P → R) := by
  intro hiff h hp
  apply h
  apply hiff.mp  -- .mp is the forward direction (modus ponens)
  exact hp

-- Applying iff in backward direction
theorem apply_iff_example2 (P Q R : Prop) : (P ↔ Q) → (P → R) → (Q → R) := by
  intro hiff h hq
  apply h
  apply hiff.mpr  -- .mpr is the backward direction (modus ponens reverse)
  exact hq

-- Iff is reflexive
theorem iff_refl (P : Prop) : P ↔ P := by
  constructor <;> intro h <;> exact h

-- Alternative: using Iff.intro directly
theorem iff_refl' (P : Prop) : P ↔ P :=
  Iff.intro id id

-- Iff is transitive
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  constructor
  · intro h
    apply hqr.mp
    apply hpq.mp
    exact h
  · intro h
    apply hpq.mpr
    apply hqr.mpr
    exact h

-- Distributivity example
theorem or_distributes_over_and (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      constructor
      · left; exact hp
      · left; exact hp
    | inr hqr =>
      obtain ⟨ hq, hr⟩ := hqr
      constructor
      · right; exact hq
      · right; exact hr
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => left; exact hp
    | inr hq =>
      cases hpr with
      | inl hp => left; exact hp
      | inr hr => right; exact ⟨hq, hr⟩


/- -------------------- SETOIDS AND LOGICAL EQUIVALENCE -------------------- -/

-- Using our earlier theorems
theorem mul_eq_0 (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · exact mult_is_0 n m
  · exact factor_is_0 n m

-- Or is associative
theorem or_assoc' (P Q R : Prop) : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  · intro h
    cases h with
    | inl hp => left; left; exact hp
    | inr hqr =>
      cases hqr with
      | inl hq => left; right; exact hq
      | inr hr => right; exact hr
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => left; exact hp
      | inr hq => right; left; exact hq
    | inr hr => right; right; exact hr

-- Using rewrite with iff (no special import needed in Lean!)
theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_0, mul_eq_0, or_assoc]


/- ------------------ EXISTENTIAL QUANTIFICATION ----------------- -/

-- Definition using existential
def Even (x : Nat) : Prop := ∃ n : Nat, x = 2 * n

#check Even -- Nat → Prop

-- Proving an existential with `use`
theorem four_is_even : Even 4 := by
  unfold Even
  exists 2

-- Alternative: direct construction
theorem four_is_even' : Even 4 :=
  ⟨2, rfl⟩

theorem exists_example_2 (n : Nat) :
    (∃ m, n = 4 + m) → (∃ o, n = 2 + o) := by
  intro ⟨m, hm⟩
  exists (2 + m)
  omega

theorem exists_example_2' (n : Nat) :
    (∃ m, n = 4 + m) → (∃ o, n = 2 + o) := by
  intro h
  obtain ⟨m, hm⟩ := h
  exists 2 + m
  omega

-- Negating existentials
theorem dist_not_exists {X : Type} (P : X → Prop) :
    (∀ x, P x) → ¬(∃ x, ¬P x) := by
  intro h1 h2
  obtain ⟨x, h3⟩ := h2
  have := h1 x
  contradiction

-- Existentials distribute over disjunction
theorem dist_exists_or {X : Type} (P Q : X → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro ⟨x, hpq⟩
    cases hpq with
    | inl hp =>
      left
      exists x
    | inr hq =>
      right
      exists x
  · intro h
    cases h with
    | inl hex =>
      obtain ⟨ x, hp⟩ := hex
      exists x
      left
      exact hp
    | inr hex =>
      obtain ⟨ x, hq⟩ := hex
      exists x
      right
      exact hq


-- More complex example with induction
theorem leb_plus_exists (n m : Nat) : n ≤ m → ∃ x, m = n + x := by
  intro h
  exists m - n
  omega  -- omega solves this arithmetic goal

-- Reverse direction
theorem plus_exists_leb (n m : Nat) : (∃ x, m = n + x) → n ≤ m := by
  intro ⟨x, h⟩
  rw [h]
  omega


/-
  PROGRAMMING WITH PROPOSITIONS

  Propositions can be defined recursively, just like functions.
  This is very convenient for expressing properties of data structures.
-/

-- List membership: x is in list l
-- This is a recursive proposition!
def In {A : Type} (x : A) (l : List A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x ∨ In x l'

-- Example: 4 is in [1,2,3,4,5]
example : In 4 [1,2,3,4,5] := by
  -- Unfold the definition
  unfold In
  right; right; right; left
  rfl

-- Using In with existentials
example (n : Nat) : In n [2,4] → ∃ n', n = 2 * n' := by
  intro h
  unfold In at h
  -- h is now: 2 = n ∨ (4 = n ∨ False)
  cases h with
  | inl h =>
    exists 1
    omega
  | inr h =>
    cases h with
    | inl h =>
      exists 2
      omega
    | inr h => contradiction

-- In is preserved by map
theorem In_map {A B : Type} (f : A → B) (l : List A) (x : A) :
    In x l → In (f x) (List.map f l) := by
  intro h
  induction l with
  | nil =>
    unfold In at h
    contradiction
  | cons x' l' ih =>
    unfold In at h ⊢
    cases h with
    | inl heq =>
      left
      rw [heq]
    | inr hin =>
      right
      exact ih hin

-- In and map: the iff version
theorem In_map_iff {A B : Type} (f : A → B) (l : List A) (y : B) :
    In y (List.map f l) ↔ ∃ x, f x = y ∧ In x l := by
  constructor
  · -- Forward direction
    intro h
    induction l with
    | nil =>
      unfold List.map In at h
      contradiction
    | cons x l' ih =>
      unfold List.map In at h
      cases h with
      | inl heq =>
        exists x
        constructor
        · exact heq
        · left; rfl
      | inr hin =>
        obtain ⟨x0, hfx0, hinx0⟩ := ih hin
        exists x0
        constructor
        · exact hfx0
        · right; exact hinx0
  · -- Backward direction
    intro ⟨x, heq, hin⟩
    rw [← heq]
    exact In_map f l x hin

-- In and append
theorem In_app_iff {A : Type} (l l' : List A) (a : A) :
    In a (l ++ l') ↔ In a l ∨ In a l' := by
  induction l with
  | nil =>
    unfold In
    simp
  | cons a' l'' ih =>
    simp only [In, List.cons_append]
    constructor
    · intro h
      cases h with
      | inl heq => left; left; exact heq
      | inr hor =>
        rw [ih] at hor  -- Apply IH to hypothesis
        cases hor with
        | inl hl => left; right; exact hl
        | inr hr => right; exact hr
    · intro h
      cases h with
      | inl hl =>
        cases hl with
        | inl heq => left; exact heq
        | inr hin => right; rw [ih]; left; exact hin
      | inr hr => right; rw [ih]; right; exact hr

-- All elements satisfy a property
def All {T : Type} (P : T → Prop) (l : List T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x ∧ All P l'

-- Relationship between All and In
theorem All_In {T : Type} (P : T → Prop) (l : List T) :
    (∀ x, In x l → P x) ↔ All P l := by
  induction l with
  | nil =>
    unfold In All
    constructor
    · intro _; trivial
    · intro _ x h; contradiction
  | cons a l' ih =>
    unfold In All
    rw [← ih]
    constructor
    · intro h
      constructor
      · apply h; left; rfl
      · intro x hin
        apply h
        right
        exact hin
    · intro ⟨hpa, hall⟩ x hor
      cases hor with
      | inl heq => rw [← heq]; exact hpa
      | inr hin => exact hall x hin

-- Combining properties based on a condition
def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  fun n => if n % 2 = 1 then Podd n else Peven n

#check combine_odd_even

-- Introduction rule for combine_odd_even
theorem combine_odd_even_intro (Podd Peven : Nat → Prop) (n : Nat) :
    (n % 2 = 1 → Podd n) →
    (n % 2 = 0 → Peven n) →
    combine_odd_even Podd Peven n := by
  intro hodd heven
  unfold combine_odd_even
  split
  · apply hodd; assumption
  · apply heven
    -- Need to prove n % 2 = 0 from ¬(n % 2 = 1)
    omega

-- Elimination rule for odd case
theorem combine_odd_even_elim_odd (Podd Peven : Nat → Prop) (n : Nat) :
    combine_odd_even Podd Peven n →
    n % 2 = 1 →
    Podd n := by
  intro h hodd
  unfold combine_odd_even at h
  split at h
  · exact h
  · omega

-- Elimination rule for even case
theorem combine_odd_even_elim_even (Podd Peven : Nat → Prop) (n : Nat) :
    combine_odd_even Podd Peven n →
    n % 2 = 0 →
    Peven n := by
  intro h heven
  unfold combine_odd_even at h
  split at h
  · omega
  · exact h

/- ------------------- APPLYING THEOREMS TO ARGUMENTS --------------- -/

-- Checking types of functions and theorems
#check Nat.add -- Nat → Nat → Nat
#check @List.reverse -- {α : Type u_1} → List α → List α

-- Our commutativity theorem
axiom add_comm : ∀ n m : Nat, n + m = m + n

-- Check its type
#check add_comm -- ∀ (n m : Nat), n + m = m + n

-- Using rewrite: the problem
theorem add_comm3_attempt (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm]
  -- We're back where we started!
  sorry

-- Solution 1: Use assert (have in Lean)
theorem add_comm3_take2 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  have h : y + z = z + y := by
    rw [add_comm]
  rw [h]

-- Solution 2: Apply theorem with specific arguments
theorem add_comm3_take3 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm]
  rw [add_comm y z]

-- Solution 3: Apply theorem to both parts explicitly
theorem add_comm3_take4 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm x (y + z)]
  rw [add_comm y z]

-- In is nonempty
theorem in_not_nil {A : Type} (x : A) (l : List A) : In x l → l ≠ [] := by
  intro h hl
  rw [hl] at h
  unfold In at h
  exact h

-- Trying to apply without specifying x
example (l : List Nat) : In 42 l → l ≠ [] := by
  intro h
  -- apply in_not_nil  -- This would fail: can't infer x
  -- Instead we need to specify x
  sorry

-- Solution 1: Specify x with named argument
theorem in_not_nil_42_take2 (l : List Nat) : In 42 l → l ≠ [] := by
  intro h
  apply in_not_nil (x := 42)
  exact h

-- Solution 2: Apply to the hypothesis
theorem in_not_nil_42_take3 (l : List Nat) : In 42 l → l ≠ [] := by
  intro h
  have := in_not_nil 42 l h  -- Apply theorem to hypothesis
  exact this

-- Solution 3: Explicit type application
theorem in_not_nil_42_take4 (l : List Nat) : In 42 l → l ≠ [] := by
  intro h
  apply (in_not_nil (A := Nat) (x := 42))
  exact h

-- Solution 4: Using underscore for inference
theorem in_not_nil_42_take5 (l : List Nat) : In 42 l → l ≠ [] := by
  intro h
  exact (in_not_nil _ _ h)

-- Using projection and theorem application
example {n : Nat} {ns : List Nat} :
    In n (List.map (fun m => m * 0) ns) → n = 0 := by
  intro h
  -- Apply In_map_iff and extract witness
  have ⟨m, hm, _⟩ := (In_map_iff _ _ _).mp h
  -- Now m * 0 = n, so n = 0
  omega


/- ------------------- WORKING WITH DECIDABLE PROPERTIES --------------

  Two ways to express claims:
  1. Bool (decidable, computational)
  2. Prop (logical, may be undecidable) ------------------ -/


-- Boolean version: computational check
def even_bool (n : Nat) : Bool :=
  n % 2 == 0

-- Propositional version: existential claim
def Even' (n : Nat) : Prop :=
  ∃ k, n = double k

-- Both ways work for concrete numbers
example : even_bool 42 = true := by
  rfl

example : Even 42 := by
  unfold Even
  exists 21

-- Helper lemmas
theorem even_double (k : Nat) : even_bool (double k) = true := by
  induction k with
  | zero =>
    rfl
  | succ k' ih =>
    simp [double, even_bool] at *
    omega

theorem even_S (n : Nat) : even_bool (n + 1) = !even_bool n := by
  simp [even_bool]
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h0 =>
      have h1 : (n + 1) % 2 = 1 := by
        simp [Nat.add_mod, h0]
      simp [h0, h1]
  | inr h1 =>
      have h0 : (n + 1) % 2 = 0 := by
        simp [Nat.add_mod, h1]
      simp [h1, h0]

theorem even_double_conv (n : Nat) :
    ∃ k, n = if even_bool n then double k else (double k).succ := by
  induction n with
  | zero =>
    exists 0
  | succ n' ih =>
    obtain ⟨k, hk⟩ := ih
    -- Coq: destruct (even n) eqn:Hev
    by_cases he : even_bool n' = true
    · exists k
      rw [even_S, he]
      simp
      simp [he] at hk
      rw [hk]
    · exists k + 1
      rw [even_S]
      rw [Bool.eq_false_iff.mpr he]
      simp
      simp [he] at hk
      rw [hk]
      simp [double]

theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    unfold double
    rw [ih]
    omega

-- Main theorem: Bool and Prop versions are equivalent
theorem even_bool_prop (n : Nat) :
    even_bool n = true ↔ Even n := by
  constructor
  · intro h
    obtain ⟨ k, hk⟩ := even_double_conv n
    rw[h] at hk
    simp at hk
    exists k
    rw [double_eq_two_mul] at hk
    exact hk
  · intro ⟨k, hk⟩
    rw [hk]
    simp[even_bool]

-- Boolean equality
theorem beq_true' (n m : Nat) :
    (n == m) = true → n = m := by
  intro h
  induction n generalizing m with
  | zero =>
    cases m
    · rfl
    · contradiction
  | succ n' ih =>
    cases m
    · contradiction
    · simp at h
      omega

theorem eqb_refl (n : Nat) : (n == n) = true := by
  induction n with
  | zero => rfl
  | succ n' ih => simp

theorem beq_eq (n m : Nat) : (n == m) = true ↔ n = m := by
  constructor
  · exact beq_true' n m
  · intro h
    rw [h]
    exact eqb_refl m

-- Example: is_even_prime
def is_even_prime (n : Nat) : Bool :=
  if n == 2 then true else false

-- Three ways to prove Even 1000

example : Even 1000 := by
  unfold Even
  exists 500

example : even_bool 1000 = true := by
  rfl

example : Even 1000 := by
  rw [← even_bool_prop]
  rfl

-- Negation is easier with booleans
example : even_bool 1001 = false := by
  rfl

-- Using boolean in proofs
theorem plus_beq_example (n m p : Nat) :
    (n == m) = true → (n + p == m + p) = true := by
  intro h
  rw [beq_eq] at h
  rw [h, beq_eq]

-- Logical connectives as booleans

theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  constructor
  · intro h
    cases b1 <;> cases b2 <;> simp at h ⊢
  · intro h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    simp

theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  constructor
  · intro h
    cases b1 <;> cases b2
    · contradiction
    · right; rfl
    · left; rfl
    · left; rfl
  · intro h
    cases h with
    | inl h => rw [h]; cases b2 <;> rfl
    | inr h => rw [h]; cases b1 <;> rfl

-- Boolean not-equal
theorem beq_neq (x y : Nat) :
    (x == y) = false ↔ x ≠ y := by
  constructor
  · intro h contra
    rw [← beq_eq] at contra
    rw [h] at contra
    contradiction
  · intro h
    by_cases heq : x = y
    · contradiction
    · cases hb : (x == y)
      · rfl
      · rw [beq_eq] at hb
        contradiction

-- List equality function
def eqb_list {A : Type} (eqb : A → A → Bool) (l1 l2 : List A) : Bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | x1 :: l1', x2 :: l2' => eqb x1 x2 && eqb_list eqb l1' l2'

-- Correctness theorem for eqb_list
theorem eqb_list_true_iff {A : Type} (eqb : A → A → Bool)
    (h : ∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2)
    (l1 l2 : List A) :
    eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
  constructor
  · -- Forward direction
    intro heq
    induction l1 generalizing l2 with
    | nil =>
      cases l2
      · rfl
      · contradiction
    | cons x1 l1' ih =>
      cases l2 with
      | nil => contradiction
      | cons x2 l2' =>
        unfold eqb_list at heq
        rw [andb_true_iff] at heq
        obtain ⟨h1, h2⟩ := heq
        rw [h] at h1
        rw[h1, ih l2' h2]
  · -- Backward direction
    intro heq
    induction l1 generalizing l2 with
    | nil =>
      rw [← heq]
      rfl
    | cons x1 l1' ih =>
      cases l2 with
      | nil => contradiction
      | cons x2 l2' =>
        unfold eqb_list
        simp only [List.cons.injEq] at heq
        obtain ⟨ hx, hl ⟩ := heq
        rw [andb_true_iff]
        constructor
        · rw [h, hx]
        · exact ih l2' hl


/- --------------------- THE LOGIC OF LEAN ------------------------------ -/

/- -------------------- FUNCTIONAL EXTENSIONALITY -----------------------

  Two functions are equal if they produce the same output for every input.

  In Coq: This requires an axiom.
  In Lean: This is BUILT-IN! Using the `funext` tactic.
-/

-- This works by computation (functions are definitionally equal)
example : (fun x => 3 + x) = (fun x => (Nat.pred 4) + x) := by
  rfl

-- This doesn't work by computation
example : (fun x => x + 1) = (fun x => 1 + x) := by
  funext x  -- Introduce x, now prove x + 1 = 1 + x
  exact Nat.add_comm x 1

-- No axiom needed! `funext` is built into Lean's type theory

-- Example: tail-recursive reverse
def rev_append {X : Type} (l1 l2 : List X) : List X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)

def tr_rev {X : Type} (l : List X) : List X :=
  rev_append l []

-- Helper lemma
theorem rev_append_nil {X : Type} (l1 l2 : List X) :
    rev_append l1 l2 = rev_append l1 [] ++ l2 := by
  induction l1 generalizing l2 with
  | nil => simp [rev_append]
  | cons x l1' ih =>
    simp only [rev_append]
    rw [ih (l2 := x :: l2), ih (l2 := [x])]
    simp [List.append_assoc, List.cons_append]

-- Main theorem: prove two functions are equal
theorem rev_append_eq {X : Type} (l1 l2 : List X) :
    rev_append l1 l2 = List.reverse l1 ++ l2 := by
  induction l1 generalizing l2 with
  | nil => simp [rev_append]
  | cons x l1' ih =>
    simp only [rev_append, List.reverse_cons]
    rw [ih]
    simp [List.append_assoc]

-- Then the main theorem is easy
theorem tr_rev_correct {X : Type} : @tr_rev X = @List.reverse X := by
  funext l
  unfold tr_rev
  rw [rev_append_eq]
  simp

-- Check which axioms we used
#print axioms tr_rev_correct

/- -------------------- CLASSICAL VS CONSTRUCTIVE LOGIC -----------------

  Lean is constructive by default but has classical logic available.
-/

-- The Law of Excluded Middle (not provable constructively)
def excluded_middle := ∀ P : Prop, P ∨ ¬P

-- Restricted version (for decidable propositions)
theorem restricted_excluded_middle (P : Prop) (b : Bool)
    (h : P ↔ b = true) : P ∨ ¬P := by
  cases b
  · right
    intro hp
    rw [h] at hp
    contradiction
  · left
    rw [h]

-- For equality on Nat (decidable)
theorem restricted_excluded_middle_eq (n m : Nat) :
    n = m ∨ n ≠ m := by
  cases Nat.decEq n m with
  | isTrue h => left; exact h
  | isFalse h => right; exact h

-- Even without full excluded middle, we can prove ¬¬(P ∨ ¬P)
theorem excluded_middle_irrefutable (P : Prop) :
    ¬¬(P ∨ ¬P) := by
  intro h
  apply h
  right
  intro hp
  apply h
  left
  exact hp

-- Classical logic is needed for some theorems
theorem not_exists_dist :
    excluded_middle →
    ∀ (X : Type) (P : X → Prop),
      ¬(∃ x, ¬P x) → (∀ x, P x) := by
  intro em X P hne x
  cases em (P x) with
  | inl hpx => exact hpx
  | inr hnpx =>
    exfalso
    apply hne
    exists x


/- ------------------- CLASSICAL LOGIC IN LEAN --------------------

  To use classical logic, import and open the Classical namespace.
-/

-- Now we can use classical reasoning
open Classical

-- Excluded middle is available
example (P : Prop) : P ∨ ¬P := em P

-- Double negation elimination
example (P : Prop) : ¬¬P → P := byContradiction

-- Proof by contradiction tactic
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  intro hp
  apply Classical.byContradiction
  intro hnq
  exact h hnq hp

def peirce := ∀ P Q : Prop, ((P → Q) → P) → P

def double_negation_elimination := ∀ P : Prop, ¬¬P → P

def de_morgan_not_and_not := ∀ P Q : Prop, ¬(¬P ∧ ¬Q) → P ∨ Q

def implies_to_or := ∀ P Q : Prop, (P → Q) → (¬P ∨ Q)

def consequentia_mirabilis := ∀ P : Prop, (¬P → P) → P

-- Peirce's law implies double negation elimination
theorem peirce_double_negation_elimination :
    peirce → double_negation_elimination := by
  intro hp
  unfold peirce double_negation_elimination at *
  intro P hnnp
  apply hp (Q := False)
  intro hnp
  exfalso
  exact hnnp hnp

-- Double negation elimination implies De Morgan's law
theorem double_negation_elimination_de_morgan_not_and_not :
    double_negation_elimination → de_morgan_not_and_not := by
  intro hdne
  unfold double_negation_elimination de_morgan_not_and_not at *
  intro P Q h
  apply hdne
  intro hnpq
  apply h
  constructor
  · intro hp
    apply hnpq
    left
    exact hp
  · intro hq
    apply hnpq
    right
    exact hq

-- De Morgan implies (P → Q) → (¬P ∨ Q)
theorem de_morgan_not_and_not_implies_to_or :
    de_morgan_not_and_not → implies_to_or := by
  intro hdm
  unfold de_morgan_not_and_not implies_to_or at *
  intro P Q hpq
  apply hdm
  intro ⟨hnnp, hnq⟩
  apply hnnp
  intro hp
  exact hnq (hpq hp)

-- (P → Q) → (¬P ∨ Q) implies excluded middle
theorem implies_to_or_excluded_middle :
    implies_to_or → excluded_middle := by
  intro hi
  unfold implies_to_or excluded_middle at *
  intro P
  have := hi P P (fun x => x)
  cases this with
  | inl h => right; exact h
  | inr h => left; exact h

-- Excluded middle implies consequentia mirabilis
theorem excluded_middle_consequentia_mirabilis :
    excluded_middle → consequentia_mirabilis := by
  intro hem
  unfold excluded_middle consequentia_mirabilis at *
  intro P hnpp
  cases hem P with
  | inl hp => exact hp
  | inr hnp => exact hnpp hnp

-- Consequentia mirabilis implies Peirce
theorem consequentia_mirabilis_peirce :
    consequentia_mirabilis → peirce := by
  intro hcm
  unfold consequentia_mirabilis peirce at *
  intro P Q hpqp
  apply hcm
  intro hnp
  exfalso
  have : ¬(P → Q) := by
    intro hpq
    exact hnp (hpqp hpq)
  apply this
  intro hp
  contradiction

-- All five principles are equivalent (and all equivalent to excluded middle)
