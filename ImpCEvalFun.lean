import Imp

-- ------------------- A BROKEN EVALUATOR ------------------

-- Omits while (returns st unchanged)
def ceval_step1 (st : State) (c : Com) : State :=
  match c with
  | .CSkip => st
  | .CAsgn x a => tUpdate st x (aeval' st a)
  | .CSeq c1 c2 =>
      let st' := ceval_step1 st c1
      ceval_step1 st' c2
  | .CIf b c1 c2 =>
      if beval' st b then ceval_step1 st c1
      else ceval_step1 st c2
  | .CWhile _ _ => st  -- bogus

-- ------------------- A STEP-INDEXED EVALUATOR -------------------

-- Returns empty_st on timeout (can't distinguish timeout from normal termination)
def ceval_step2 (st : State) (c : Com) (i : Nat) : State :=
  match i with
  | 0 => empty_st
  | .succ i' =>
    match c with
    | .CSkip => st
    | .CAsgn x a => tUpdate st x (aeval' st a)
    | .CSeq c1 c2 =>
        let st' := ceval_step2 st c1 i'
        ceval_step2 st' c2 i'
    | .CIf b c1 c2 =>
        if beval' st b then ceval_step2 st c1 i'
        else ceval_step2 st c2 i'
    | .CWhile b c1 =>
        if beval' st b then
          let st' := ceval_step2 st c1 i'
          ceval_step2 st' c i'
        else st

-- ------------------- STEP-INDEXED WITH OPTION ------------------

-- Returns None on timeout, Some st on normal termination
def ceval_step3 (st : State) (c : Com) (i : Nat) : Option State :=
  match i with
  | 0 => none
  | .succ i' =>
    match c with
    | .CSkip => some st
    | .CAsgn x a => some (tUpdate st x (aeval' st a))
    | .CSeq c1 c2 =>
        match ceval_step3 st c1 i' with
        | some st' => ceval_step3 st' c2 i'
        | none => none
    | .CIf b c1 c2 =>
        if beval' st b then ceval_step3 st c1 i'
        else ceval_step3 st c2 i'
    | .CWhile b c1 =>
        if beval' st b then
          match ceval_step3 st c1 i' with
          | some st' => ceval_step3 st' c i'
          | none => none
        else some st

-- ------------------- CLEANER VERSION WITH DO NOTATION -------------------

-- Lean's Option has Monad instance, so do notation replaces LETOPT
def ceval_step (st : State) (c : Com) (i : Nat) : Option State :=
  match i with
  | 0 => none
  | .succ i' =>
    match c with
    | .CSkip => some st
    | .CAsgn x a => some (tUpdate st x (aeval' st a))
    | .CSeq c1 c2 => do
        let st' ← ceval_step st c1 i'
        ceval_step st' c2 i'
    | .CIf b c1 c2 =>
        if beval' st b then ceval_step st c1 i'
        else ceval_step st c2 i'
    | .CWhile b c1 =>
        if beval' st b then do
          let st' ← ceval_step st c1 i'
          ceval_step st' c i'
        else some st

-- ------------------- TESTING -------------------

def test_ceval (st : State) (c : Com) : Option (Nat × Nat × Nat) :=
  match ceval_step st c 500 with
  | none => none
  | some st => some (st X, st Y, st Z)

example : test_ceval empty_st
    (.CSeq
      (.CAsgn X (.ANum 2))
      (.CIf (.BLe (.AId X) (.ANum 1))
        (.CAsgn Y (.ANum 3))
        (.CAsgn Z (.ANum 4))))
    = some (2, 0, 4) := rfl

-- pup_to_n: sum 1 to X into Y
def pup_to_n' : Com :=
  .CSeq
    (.CAsgn Y (.ANum 0))
    (.CWhile (.BGt (.AId X) (.ANum 0))
      (.CSeq
        (.CAsgn Y (.APlus (.AId Y) (.AId X)))
        (.CAsgn X (.AMinus (.AId X) (.ANum 1)))))

example : test_ceval (tUpdate empty_st X 5) pup_to_n' = some (0, 15, 0) := rfl

-- ------------------- RELATIONAL VS STEP-INDEXED -------------------

-- peven: sets Z to 0 if X even, 1 if odd
def peven : Com :=
  .CSeq
    (.CAsgn Z (.ANum 0))
    (.CWhile (.BGt (.AId X) (.ANum 0))
      (.CSeq
        (.CIf (.BEq (.AId Z) (.ANum 0))
          (.CAsgn Z (.ANum 1))
          (.CAsgn Z (.ANum 0)))
        (.CAsgn X (.AMinus (.AId X) (.ANum 1)))))

example : test_ceval (tUpdate empty_st X 0) peven = some (0, 0, 0) := rfl
example : test_ceval (tUpdate empty_st X 1) peven = some (0, 0, 1) := rfl
example : test_ceval (tUpdate empty_st X 2) peven = some (0, 0, 0) := rfl
example : test_ceval (tUpdate empty_st X 3) peven = some (0, 0, 1) := rfl
example : test_ceval (tUpdate empty_st X 4) peven = some (0, 0, 0) := rfl

-- Step-indexed evaluation implies relational evaluation
theorem ceval_step__ceval : ∀ c (st st' : State),
    (∃ i, ceval_step st c i = some st') →
    CEval c st st' := by
  intro c st st' ⟨i, H⟩
  revert c st st' H
  induction i with
  | zero =>
    intro c st st' H
    simp [ceval_step] at H
  | succ i' ih =>
    intro c st st' H
    cases c with
    | CSkip =>
      simp [ceval_step] at H
      rw [H]
      exact CEval.E_Skip st'
    | CAsgn x a =>
      simp [ceval_step] at H
      rw [← H]
      exact CEval.E_Asgn st a (aeval' st a) x rfl
    | CSeq c1 c2 =>
      simp [ceval_step] at H
      cases Heq1 : ceval_step st c1 i' with
      | none => simp [Heq1] at H
      | some st'' =>
        simp [Heq1] at H
        exact CEval.E_Seq c1 c2 st st'' st' (ih c1 st st'' Heq1) (ih c2 st'' st' H)
    | CIf b c1 c2 =>
      simp [ceval_step] at H
      cases Hb : beval' st b with
      | true =>
        simp [Hb] at H
        exact CEval.E_IfTrue st st' b c1 c2 Hb (ih c1 st st' H)
      | false =>
        simp [Hb] at H
        exact CEval.E_IfFalse st st' b c1 c2 Hb (ih c2 st st' H)
    | CWhile b c =>
      simp [ceval_step] at H
      cases Hb : beval' st b with
      | false =>
        simp [Hb] at H
        subst H
        exact CEval.E_WhileFalse b st c Hb
      | true =>
        simp [Hb] at H
        cases Heq1 : ceval_step st c i' with
        | none => simp [Heq1] at H
        | some st'' =>
          simp [Heq1] at H
          exact CEval.E_WhileTrue st st'' st' b c Hb
            (ih c st st'' Heq1)
            (ih (Com.CWhile b c) st'' st' H)

-- Monotonicity: more steps doesn't change result
theorem ceval_step_more : ∀ i1 i2 st st' c,
    i1 ≤ i2 →
    ceval_step st c i1 = some st' →
    ceval_step st c i2 = some st' := by
  intro i1
  induction i1 with
  | zero =>
    intro i2 st st' c _ H
    simp [ceval_step] at H
  | succ i1' ih =>
    intro i2 st st' c Hle H
    cases i2 with
    | zero => omega
    | succ i2' =>
      have Hle' : i1' ≤ i2' := by omega
      cases c with
      | CSkip =>
        simp [ceval_step] at H ⊢
        exact H
      | CAsgn x a =>
        simp [ceval_step] at H ⊢
        exact H
      | CSeq c1 c2 =>
        simp [ceval_step] at H ⊢
        cases Heq1 : ceval_step st c1 i1' with
        | none => simp [Heq1] at H
        | some st'' =>
          simp [Heq1] at H
          have H1 : ceval_step st c1 i2' = some st'' := ih i2' st st'' c1 Hle' Heq1
          simp [H1]
          exact ih i2' st'' st' c2 Hle' H
      | CIf b c1 c2 =>
        simp [ceval_step] at H ⊢
        cases Hb : beval' st b with
        | true =>
          simp [Hb] at H ⊢
          exact ih i2' st st' c1 Hle' H
        | false =>
          simp [Hb] at H ⊢
          exact ih i2' st st' c2 Hle' H
      | CWhile b c =>
        simp [ceval_step] at H ⊢
        cases Hb : beval' st b with
        | false =>
          simp [Hb] at H ⊢
          exact H
        | true =>
          simp [Hb] at H ⊢
          cases Heq1 : ceval_step st c i1' with
          | none => simp [Heq1] at H
          | some st'' =>
            simp [Heq1] at H
            have H1 : ceval_step st c i2' = some st'' := ih i2' st st'' c Hle' Heq1
            simp [H1]
            exact ih i2' st'' st' (.CWhile b c) Hle' H

-- Helper lemma

theorem le_plus_l (a b : Nat) : a ≤ a + b := Nat.le_add_right a b
theorem le_plus_r (a b : Nat) : b ≤ a + b := Nat.le_add_left b a

-- Relational evaluation implies step-indexed evaluation
-- Relational evaluation implies step-indexed evaluation
theorem ceval__ceval_step : ∀ c (st st' : State),
    CEval c st st' →
    ∃ i, ceval_step st c i = some st' := by
  intro c st st' Hce
  induction Hce with
  | E_Skip st =>
    exact ⟨1, rfl⟩
  | E_Asgn st a n x Ha =>
    exact ⟨1, by simp [ceval_step, Ha]⟩
  | E_Seq c1 c2 st st' st'' _ _ ih1 ih2 =>
    let ⟨i1, Hi1⟩ := ih1
    let ⟨i2, Hi2⟩ := ih2
    have H1 : ceval_step st c1 (i1 + i2) = some st' :=
      ceval_step_more i1 (i1 + i2) st st' c1 (le_plus_l i1 i2) Hi1
    have H2 : ceval_step st' c2 (i1 + i2) = some st'' :=
      ceval_step_more i2 (i1 + i2) st' st'' c2 (le_plus_r i1 i2) Hi2
    exact ⟨i1 + i2 + 1, by simp [ceval_step, H1, H2]⟩
  | E_IfTrue st st' b c1 c2 Hb _ ih =>
    let ⟨i, Hi⟩ := ih
    exact ⟨i + 1, by simp [ceval_step, Hb, Hi]⟩
  | E_IfFalse st st' b c1 c2 Hb _ ih =>
    let ⟨i, Hi⟩ := ih
    exact ⟨i + 1, by simp [ceval_step, Hb, Hi]⟩
  | E_WhileFalse b st c Hb =>
    exact ⟨1, by simp [ceval_step, Hb]⟩
  | E_WhileTrue st st' st'' b c Hb _ _ ih1 ih2 =>
    let ⟨i1, Hi1⟩ := ih1
    let ⟨i2, Hi2⟩ := ih2
    have H1 : ceval_step st c (i1 + i2) = some st' :=
      ceval_step_more i1 (i1 + i2) st st' c (le_plus_l i1 i2) Hi1
    have H2 : ceval_step st' (Com.CWhile b c) (i1 + i2) = some st'' :=
      ceval_step_more i2 (i1 + i2) st' st'' (Com.CWhile b c) (le_plus_r i1 i2) Hi2
    exact ⟨i1 + i2 + 1, by simp [ceval_step, Hb, H1, H2]⟩

-- The two definitions coincide
theorem ceval_and_ceval_step_coincide : ∀ c (st st' : State),
    CEval c st st' ↔ ∃ i, ceval_step st c i = some st' :=
  fun c st st' => Iff.intro (ceval__ceval_step c st st') (ceval_step__ceval c st st')

-- ------------------- DETERMINISM AGAIN -------------------

theorem ceval_deterministic' : ∀ c (st st1 st2 : State),
    CEval c st st1 →
    CEval c st st2 →
    st1 = st2 := by
  intro c st st1 st2 He1 He2
  have ⟨i1, E1⟩ := ceval__ceval_step c st st1 He1
  have ⟨i2, E2⟩ := ceval__ceval_step c st st2 He2
  have E1' := ceval_step_more i1 (i1 + i2) st st1 c (le_plus_l i1 i2) E1
  have E2' := ceval_step_more i2 (i1 + i2) st st2 c (le_plus_r i1 i2) E2
  simp [E1'] at E2'
  exact E2'

