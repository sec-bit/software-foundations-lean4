theorem plus_n_0 : forall n : Nat, n + 0 = n := by
  intro n
  rfl

theorem plus_n_0' : forall n : Nat, n + 0 = n := by
  intro n
  simp

theorem plus_r_1 : forall n : Nat, n + 1 = Nat.succ n := by
  intro n
  rfl

theorem mult_r_0 : forall n : Nat, n*0=0 := by
  intro n
  rfl

theorem plus_id_example : forall n m : Nat,
  n = m -> n + n = m + m := by
  intro n m
  intro h
  rw [h]


-- EXERCISE 1 --

theorem plus_id_exercise : forall n m o : Nat,
  n = m -> m = o -> n + m = m + o := by
  sorry


#check Nat.zero_mul
-- Nat.zero_mul (n : Nat) : 0 * n = 0
#check Nat.mul_succ
-- Nat.mul_succ (n m : Nat) : n * m.succ = n * m + n

theorem mult_0_p_0_q : forall p q : Nat,
  0*p + 0*q = 0 := by
  intro p q
  rw[Nat.zero_mul]
  rw[Nat.zero_mul]



-- PROOF BY CASE ANALYSIS

theorem negb_involutive (b : Bool) : !(!b) = b := by
  cases b with
  | true => rfl
  | false =>  rfl

theorem plus_1_neq_0 (n : Nat) : ((n + 1) == 0) = false := by
  cases n with
  | zero => rfl
  | succ n' => rfl

theorem andb_commutative_bad (b c : Bool) : (b && c) = (c && b) := by
  cases b with
  | true =>
      cases c with
      | true => rfl
      | false => rfl
  | false =>
      cases c with
      | true => rfl
      | false => rfl

theorem andb_commutative (b c : Bool) : (b && c) = (c && b) := by
  match b, c with
  | true, true   => rfl
  | true, false  => rfl
  | false, true  => rfl
  | false, false => rfl

def isZero (n : Nat) : Bool :=
  match n with
  | 0   => true
  | _   => false

theorem check_isZero (n : Nat) :
    isZero n = true → n = 0 := by
  intro h_eq
  cases h_n : n with
  | zero => simp
  | succ n' => rw [h_n] at h_eq
               simp [isZero] at h_eq


-- EXERCISE 2 --
theorem andb_true_elim2 ( b c : Bool) :
  (b && c) = true -> c = true := by
  sorry

theorem zero_nbeq_plus_1 ( n : Nat) :
   (0 == ( n  +1)) = false := by
   sorry
