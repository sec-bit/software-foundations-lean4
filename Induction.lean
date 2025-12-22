-- Induction: Proof by Induction
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html

-- # Seperate Compilation
import Basics

-- # Proof by Induction
-- theorem add_zero_r_firsttry : ∀ n : Nat, n + 0 = n := by
--   intro n
--   -- simp: does nothing! (but, unlike Coq, lean does not fail)
--   sorry

-- theorem add_zero_r_secondtry : ∀ n : Nat, n + 0 = n := by
--   intro n
--   match n with
--   | .zero => rfl
--   | .succ n' =>
--     -- simp: does nothing! (but, unlike Coq, lean does not fail)
--     sorry -- We get stuck here

theorem add_zero_r : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp <;> rewrite [ih] <;> rfl

theorem sub_self : ∀ n : Nat, n - n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp <;> rewrite [ih] <;> rfl

-- ### Exercise: 2 stars, standard, especially useful (basic_induction)
theorem mul_zero_r : ∀ n : Nat, n * 0 = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp <;> rewrite [ih] <;> rfl

theorem add_succ : ∀ n m : Nat, .succ (n + m) = n + .succ m := by
  intro n m
  rfl

theorem succ_add : ∀ n m :Nat, .succ n + m = .succ (n + m) := by
  intro n m
  induction m with
  | zero => rfl
  | succ m' ih => rw [Nat.add_succ, Nat.add_succ, ih]

theorem add_comm : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction n with
  | zero => rw [zero_add]
            rfl
  | succ n' ih => rw [succ_add]
                  rw[ Nat.add_succ]
                  rw [ih]

theorem add_assoc : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  intro n m p
  induction p with
  | zero => rfl
  | succ p' ih => rw[Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

-- ### Exercise: 2 stars, standard (double_plus)
def double (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n' => .succ (.succ (double n'))

theorem double_plus : ∀ n : Nat, double n = n + n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp [double]
                  rw[ih]
                  rw[Nat.add_succ]
                  rw[Nat.add_succ]
                  rw[Nat.add_succ]
                  rw[Nat.add_succ]
                  rw[succ_add]
                  rw[succ_add]


-- ### Exercise: 2 stars, standard (eqb_refl)
theorem eqb_refl : ∀ n : Nat, (n =? n) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => exact ih

-- ### Exercise: 2 stars, standard, optional (even_S)
theorem even_succ : ∀ n : Nat, even (.succ n) = not (even n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp[even]
                  rw[ih]
                  simp


-- # Proofs Within Proofs
-- In Lean, we use `have` to achieve similar effect to Coq's `assert`.

theorem mul_zero_plus' : ∀ n m : Nat, (n + 0 + 0) * m = n * m := by
  intro n m
  have h : n + 0 + 0 = n := by
    rewrite [add_comm] <;> simp <;> rewrite [add_comm] <;> rfl
  rewrite [h]
  rfl

-- theorem plus_rearrange_firsttry :
--   ∀ n m p q : Nat,
--   (n + m) + (p + q) = (m + n) + (p + q)
-- := by
--   intro n m p q
--   rewrite [add_comm] -- Lean rewrites the wrong plus!
--   sorry

theorem plus_rearrange_secondtry :
  ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q)
:= by
  intro n m p q
  rewrite [add_comm n m] -- You can specify which term!
  rfl

theorem plus_rearrange :
  ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q)
:= by
  intro n m p q
  have h : n + m = m + n := by -- Or declare an intermediate proof term
    rewrite [add_comm] <;> rfl
  rewrite [h]
  rfl

-- # Formal vs. Informal Proofs
-- NOTE: We'll skip `Exercise: 2 stars, advanced, especially useful (add_comm_informal)`
-- and `Exercise: 2 stars, standard, optional (eqb_refl_informal)` as they are
-- about writing informal proofs.

-- # More Exercises

-- ### Exercise: 3 stars, standard, especially useful (mul_comm)
theorem add_shuffle3 : ∀ n m p : Nat, n + (m + p) = m + (n + p) := by
  intro n m p
  rw [add_assoc, add_comm n m, <- add_assoc]

theorem mul_comm : ∀ m n : Nat, m * n = n * m := by
  intro n m
  induction n with
  | zero => rw[zero_mul]
            rfl
  | succ n' ih => rw[Nat.succ_mul, ih, Nat.mul_succ]

-- ### Exercise: 3 stars, standard, optional (more_exercises)
theorem leb_refl : ∀ n : Nat, (n <=? n) = MyBool.true := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => exact ih

theorem zero_neq_succ : ∀ n : Nat, (0 =? .succ n) = MyBool.false := by
  intro n
  rfl

theorem andb_false_r : ∀ b : MyBool, b my&& .false = .false := by
  intro b
  cases b <;> rfl

theorem succ_neqb_zero : ∀ n : Nat, (.succ n =? 0) = MyBool.false := by
  intro n
  rfl

theorem one_mul : ∀ n : Nat, 1 * n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => rw[Nat.mul_succ, ih]

theorem all3_spec : ∀ b c : MyBool,
  orb (andb b c) (orb (negb b) (negb c)) = .true
:= by
  intro b c
  cases b <;> cases c <;> rfl

theorem mul_plus_distr_r : ∀ n m p : Nat, (n + m) * p = (n * p) + (m * p) := by
  intro n m p
  induction p with
  | zero =>
    rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ p' ih =>
    rw [Nat.mul_succ, ih]
    rw [Nat.mul_succ, Nat.mul_succ]
    simp [ Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem mul_assoc : ∀ n m p : Nat, (n * m) * p = n * (m * p) := by
  intro n m p
  -- CRITICAL: Induct on 'n', not 'p'
  induction n with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | succ n ih =>
    rw [Nat.succ_mul]
    rw [mul_plus_distr_r]
    rw [Nat.succ_mul]
    rw [ih]

-- ### Exercise: 2 stars, standard, optional (add_shuffle3')
theorem add_shuffle3' : ∀ n m p : Nat, n + (m + p) = m + (n + p) := by
  intro n m p
  rw [add_assoc, add_comm n m, ←add_assoc]

-- # Nat to Bin and Back to Nat

-- ### Exercise: 3 stars, standard, especially useful (binary_commute)
theorem bin_to_nat_pres_incr : ∀ b : Bin,
  bin_to_nat (incr b) = 1 + (bin_to_nat b)
:= by
  intro b
  induction b with
  | z => rfl
  | b0 b ih => rfl
  | b1 b ih =>
    dsimp [incr, bin_to_nat]
    rw [ih]
    -- Goal: 2 * (1 + bin_to_nat b) = 1 + (1 + 2 * bin_to_nat b)
    -- 2 + 2*val = 2 + 2*val
    rw [Nat.mul_add, add_assoc]

-- ### Exercise: 3 stars, standard (nat_bin_nat)
def nat_to_bin (n : Nat) : Bin :=
  match n with
  | 0 => .z
  | n' + 1 => incr (nat_to_bin n')

theorem nat_bin_nat : ∀ n : Nat, bin_to_nat (nat_to_bin n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [nat_to_bin]
                 rw [bin_to_nat_pres_incr, ih]
                 rw[add_comm]

-- # Bin to Nat and Back to Bin (Advanced)
-- theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b := by
--   sorry -- does not hold

-- ### Exercise: 2 stars, advanced (double_bin)
theorem double_incr : ∀ n : Nat, double (.succ n) = .succ (.succ (double n)) := by
  intro n
  simp [double]

def double_bin (b : Bin) : Bin :=
  match b with
  | .z => .z
  | _ => .b0 b

example : double_bin .z = .z := by
  rfl

theorem double_incr_bin :
  ∀ b : Bin,
  double_bin (incr b) = incr (incr (double_bin b))
:= by
  intro b
  induction b with
  | z => rfl
  | b0 b ih => rfl
  | b1 b ih => rfl


-- ### Exercise: 4 stars, advanced (bin_nat_bin)
def normalize (b : Bin) : Bin :=
  match b with
  | .z => .z
  | .b0 b' =>
    match normalize b' with
    | .z => .z
    | b'' => .b0 b''
  | .b1 b' => .b1 (normalize b')
