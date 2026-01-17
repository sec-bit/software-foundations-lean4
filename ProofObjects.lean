/-
  ProofObjects: The Curry-Howard Correspondence
-/


inductive ev : Nat -> Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat)(H : ev n) : ev (n+2)

open ev

#check ev.ev_SS  -- (n : Nat) → ev n → ev (n + 2)

-- Building Proof Objects with Tactics

theorem ev_4 : ev 4 := by
  apply ev_SS
  apply ev_SS
  apply ev_0


#print ev_4


#check (ev_SS 2 (ev_SS 0 ev_0) : ev 4)


theorem ev_4' : ev 4 := by
  exact ev_SS 2 (ev_SS 0 ev_0)


theorem ev_4'' : ev 4 := by
  apply ev_SS  -- Coq Show Proof: (ev_SS ?n ?H)
  apply ev_SS  -- Coq Show Proof: (ev_SS _ (ev_SS ?n ?H))
  apply ev_0   -- Coq Show Proof: (ev_SS 2 (ev_SS 0 ev_0))

/-- Term-mode proof: no tactics, just construct the evidence directly. -/
def ev_4''' : ev 4 := ev_SS 2 (ev_SS 0 ev_0)

#print ev_4
#print ev_4'
#print ev_4''
#print ev_4'''

/-- ev 8: proof using tactic -/
theorem ev_8 : ev 8 := by
  exact ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))

/-- ev 8: term-mode proof -/
def ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))

#print ev_8
#print ev_8'

theorem ev_plus4 : ∀ n, ev n → ev (n + 4) := by
  intro n H
  apply ev_SS
  apply ev_SS
  exact H


def ev_plus4' : ∀ n, ev n → ev (n + 4) :=
  fun (n : Nat) => fun (H : ev n) =>
    ev_SS (n + 2) (ev_SS n H)

/-- Alternative: arguments before the colon. -/
def ev_plus4'' (n : Nat) (H : ev n) : ev (n + 4) :=
  ev_SS (n + 2) (ev_SS n H)

#check ev_plus4'
#check ev_plus4''

def ev_plus2 : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

def ev_plus2' : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

def ev_plus2'' : Prop :=
  ∀ n, ev n → ev (n + 2)

def add1 : Nat → Nat := by
  intro n
  exact Nat.succ n

#print add1
#eval add1 2  -- 3

-- ------------------ LOGICAL CONNECTIVES AS INDUCTIVE TYPES -----------------------

-- Coq defines And, Or, Ex, True, False as inductive types.
-- Lean has these built-in with the same structure:
--
--   Coq                    Lean
--   conj HP HQ             And.intro hp hq  or  ⟨hp, hq⟩
--   or_introl HP           Or.inl hp
--   or_intror HQ           Or.inr hq
--   ex_intro P x Hx        Exists.intro x hx  or  ⟨x, hx⟩
--   I                      True.intro  or  trivial
--   match contra with end  False.elim contra  or  nomatch contra

-- ------------------ CONJUNCTION -----------------------

#print And

-- Projection: extract left component (tactic)
theorem proj1' (P Q : Prop) (HPQ : P ∧ Q) : P := by
  obtain ⟨HP, _⟩ := HPQ
  exact HP

-- And is commutative (tactic)
theorem and_comm' (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨HP, HQ⟩
    exact ⟨HQ, HP⟩
  · intro ⟨HQ, HP⟩
    exact ⟨HP, HQ⟩

-- Projection: term-mode with pattern matching
def proj1'' (P Q : Prop) (HPQ : P ∧ Q) : P :=
  match HPQ with
  | ⟨HP, _⟩ => HP

-- Or use .left accessor directly
def proj1''' (P Q : Prop) (HPQ : P ∧ Q) : P := HPQ.left

-- Auxiliary for and_comm (term-mode)
def and_comm'_aux (P Q : Prop) (H : P ∧ Q) : Q ∧ P :=
  match H with
  | ⟨HP, HQ⟩ => ⟨HQ, HP⟩

-- And commutativity (term-mode)
def and_comm'' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
  ⟨and_comm'_aux P Q, and_comm'_aux Q P⟩

-- conj_fact: P ∧ Q → Q ∧ R → P ∧ R
def conj_fact (P Q R : Prop) (HPQ : P ∧ Q) (HQR : Q ∧ R) : P ∧ R :=
  match HPQ, HQR with
  | ⟨HP, _⟩, ⟨_, HR⟩ => ⟨HP, HR⟩

-- ------------------ DISJUNCTION -----------------------

#print Or

-- Left injection (term-mode)
def inj_l (P Q : Prop) (HP : P) : P ∨ Q := Or.inl HP

-- Left injection (tactic)
theorem inj_l' (P Q : Prop) (HP : P) : P ∨ Q := by
  left
  exact HP

-- Or elimination (term-mode)
def or_elim (P Q R : Prop) (HPQ : P ∨ Q) (HPR : P → R) (HQR : Q → R) : R :=
  match HPQ with
  | Or.inl HP => HPR HP
  | Or.inr HQ => HQR HQ

-- Or elimination (tactic)
theorem or_elim' (P Q R : Prop) (HPQ : P ∨ Q) (HPR : P → R) (HQR : Q → R) : R := by
  cases HPQ with
  | inl HP => exact HPR HP
  | inr HQ => exact HQR HQ

-- Or commutativity (tactic)
theorem or_commut (P Q : Prop) (HPQ : P ∨ Q) : Q ∨ P := by
  cases HPQ with
  | inl HP => right; exact HP
  | inr HQ => left; exact HQ

-- Or commutativity (term-mode)
def or_commut' (P Q : Prop) (HPQ : P ∨ Q) : Q ∨ P :=
  match HPQ with
  | Or.inl HP => Or.inr HP
  | Or.inr HQ => Or.inl HQ

-- ------------------ EXISTENTIAL QUANTIFICATION -----------------------

#print Exists

#check (⟨4, ev_SS 2 (ev_SS 0 ev_0)⟩ : ∃ n, ev n)

-- Some natural is even: witness is 4
def some_nat_is_even : ∃ n, ev n :=
  ⟨4, ev_SS 2 (ev_SS 0 ev_0)⟩

-- There exists n such that n+1 is even: witness is 1
def ex_ev_Sn : ∃ n, ev (n + 1) :=
  ⟨1, ev_SS 0 ev_0⟩

-- Distribute exists over or
def dist_exists_or (X : Type) (P Q : X → Prop)
    (H : ∃ x, P x ∨ Q x) : (∃ x, P x) ∨ (∃ x, Q x) :=
  match H with
  | ⟨x, Hx⟩ =>
    match Hx with
    | Or.inl HPx => Or.inl ⟨x, HPx⟩
    | Or.inr HQx => Or.inr ⟨x, HQx⟩

-- Map over existential
def ex_map (A : Type) (P Q : A → Prop)
    (H : ∀ x, P x → Q x) (HP : ∃ x, P x) : ∃ x, Q x :=
  match HP with
  | ⟨x, Hx⟩ => ⟨x, H x Hx⟩

-- ------------------ TRUE AND FALSE -----------------------

#print True
#print False

-- Anything implies True
def p_implies_true (P : Prop) (_ : P) : True := True.intro

-- From False, anything follows (nomatch)
def false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

-- Ex falso quodlibet (nomatch)
def ex_falso_quodlibet' (P : Prop) (contra : False) : P :=
  nomatch contra

-- Alternative: use False.elim
def ex_falso_quodlibet'' (P : Prop) (contra : False) : P :=
  False.elim contra
