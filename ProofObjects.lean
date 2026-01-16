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
