-- ProofObjects: The Curry-Howard Correspondence

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

def ev_4''' : ev 4 := ev_SS 2 (ev_SS 0 ev_0)

#print ev_4
#print ev_4'
#print ev_4''
#print ev_4'''

theorem ev_8 : ev 8 := by
  exact ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))

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


-- ------------------ CONJUNCTION -----------------------

#print And

theorem proj1' (P Q : Prop) (HPQ : P ∧ Q) : P := by
  obtain ⟨HP, _⟩ := HPQ
  exact HP

theorem and_comm' (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨HP, HQ⟩
    exact ⟨HQ, HP⟩
  · intro ⟨HQ, HP⟩
    exact ⟨HP, HQ⟩

def proj1'' (P Q : Prop) (HPQ : P ∧ Q) : P :=
  match HPQ with
  | ⟨HP, _⟩ => HP

def proj1''' (P Q : Prop) (HPQ : P ∧ Q) : P := HPQ.left

def and_comm'_aux (P Q : Prop) (H : P ∧ Q) : Q ∧ P :=
  match H with
  | ⟨HP, HQ⟩ => ⟨HQ, HP⟩

def and_comm'' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
  ⟨and_comm'_aux P Q, and_comm'_aux Q P⟩

def conj_fact (P Q R : Prop) (HPQ : P ∧ Q) (HQR : Q ∧ R) : P ∧ R :=
  match HPQ, HQR with
  | ⟨HP, _⟩, ⟨_, HR⟩ => ⟨HP, HR⟩

-- ------------------ DISJUNCTION -----------------------

#print Or

def inj_l (P Q : Prop) (HP : P) : P ∨ Q := Or.inl HP

theorem inj_l' (P Q : Prop) (HP : P) : P ∨ Q := by
  left
  exact HP

def or_elim (P Q R : Prop) (HPQ : P ∨ Q) (HPR : P → R) (HQR : Q → R) : R :=
  match HPQ with
  | Or.inl HP => HPR HP
  | Or.inr HQ => HQR HQ

theorem or_elim' (P Q R : Prop) (HPQ : P ∨ Q) (HPR : P → R) (HQR : Q → R) : R := by
  cases HPQ with
  | inl HP => exact HPR HP
  | inr HQ => exact HQR HQ

theorem or_commut (P Q : Prop) (HPQ : P ∨ Q) : Q ∨ P := by
  cases HPQ with
  | inl HP => right; exact HP
  | inr HQ => left; exact HQ

def or_commut' (P Q : Prop) (HPQ : P ∨ Q) : Q ∨ P :=
  match HPQ with
  | Or.inl HP => Or.inr HP
  | Or.inr HQ => Or.inl HQ

-- ------------------ EXISTENTIAL QUANTIFICATION -----------------------

#print Exists

#check (⟨4, ev_SS 2 (ev_SS 0 ev_0)⟩ : ∃ n, ev n)

def some_nat_is_even : ∃ n, ev n :=
  ⟨4, ev_SS 2 (ev_SS 0 ev_0)⟩

def ex_ev_Sn : ∃ n, ev (n + 1) :=
  ⟨1, ev_SS 0 ev_0⟩

def dist_exists_or (X : Type) (P Q : X → Prop)
    (H : ∃ x, P x ∨ Q x) : (∃ x, P x) ∨ (∃ x, Q x) :=
  match H with
  | ⟨x, Hx⟩ =>
    match Hx with
    | Or.inl HPx => Or.inl ⟨x, HPx⟩
    | Or.inr HQx => Or.inr ⟨x, HQx⟩

def ex_map (A : Type) (P Q : A → Prop)
    (H : ∀ x, P x → Q x) (HP : ∃ x, P x) : ∃ x, Q x :=
  match HP with
  | ⟨x, Hx⟩ => ⟨x, H x Hx⟩

-- ------------------ TRUE AND FALSE -----------------------

#print True
#print False

def p_implies_true (P : Prop) (_ : P) : True := True.intro

def false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

def ex_falso_quodlibet' (P : Prop) (contra : False) : P :=
  nomatch contra

def ex_falso_quodlibet'' (P : Prop) (contra : False) : P :=
  False.elim contra

-- ------------------ EQUALITY -----------------------

#print Eq

theorem four : 2 + 2 = 1 + 3 := by
  rfl

def four' : 2 + 2 = 1 + 3 := Eq.refl 4

def four'' : 2 + 2 = 1 + 3 := rfl

def singleton (X : Type) (x : X) : [] ++ [x] = x :: [] := rfl

def eq_add (n1 n2 : Nat) (Heq : n1 = n2) : n1 + 1 = n2 + 1 :=
  match Heq with
  | rfl => rfl

theorem eq_add' (n1 n2 : Nat) (Heq : n1 = n2) : n1 + 1 = n2 + 1 := by
  cases Heq
  rfl

def eq_cons (X : Type) (h1 h2 : X) (t1 t2 : List X)
    (Heq : h1 = h2) (Teq : t1 = t2) : h1 :: t1 = h2 :: t2 :=
  match Heq, Teq with
  | rfl, rfl => rfl

theorem equality_leibniz_equality (X : Type) (x y : X)
    (H : x = y) (P : X → Prop) (Hx : P x) : P y := by
  cases H
  exact Hx

def equality_leibniz_equality_term (X : Type) (x y : X)
    (Heq : x = y) : ∀ P : X → Prop, P x → P y :=
  match Heq with
  | rfl => fun _ H => H

theorem leibniz_equality_equality (X : Type) (x y : X)
    (H : ∀ P : X → Prop, P x → P y) : x = y :=
  H (fun z => x = z) rfl


-- ------------------ TRUSTED COMPUTING BASE -----------------------

-- This would fail: non-exhaustive match
-- def or_bogus (P Q : Prop) (A : P ∨ Q) : P :=
--   match A with
--   | Or.inl H => H
--   -- missing Or.inr case!

-- This would fail: non-terminating
-- def infinite_loop (X : Type) (n : Nat) : X :=
--   infinite_loop X n
--
-- def falso : False := infinite_loop False 0

-- ------------------ MORE EXERCISES -----------------------

def and_assoc' (P Q R : Prop) (H : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R :=
  match H with
  | ⟨HP, ⟨HQ, HR⟩⟩ => ⟨⟨HP, HQ⟩, HR⟩

def or_distributes_over_and (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  ⟨fun H =>
    match H with
    | Or.inl HP => ⟨Or.inl HP, Or.inl HP⟩
    | Or.inr ⟨HQ, HR⟩ => ⟨Or.inr HQ, Or.inr HR⟩,
   fun H =>
    match H with
    | ⟨Or.inl HP, _⟩ => Or.inl HP
    | ⟨_, Or.inl HP⟩ => Or.inl HP
    | ⟨Or.inr HQ, Or.inr HR⟩ => Or.inr ⟨HQ, HR⟩⟩

def double_neg (P : Prop) (H : P) : ¬¬P :=
  fun HnotP => HnotP H

def contradiction_implies_anything (P Q : Prop) (contra : P ∧ ¬P) : Q :=
  match contra with
  | ⟨HP, HNA⟩ => nomatch HNA HP

def de_morgan_not_or (P Q : Prop) (HPQ : ¬(P ∨ Q)) : ¬P ∧ ¬Q :=
  ⟨fun HP => HPQ (Or.inl HP), fun HQ => HPQ (Or.inr HQ)⟩

def curry' (P Q R : Prop) (Hpair : P ∧ Q → R) (HP : P) (HQ : Q) : R :=
  Hpair ⟨HP, HQ⟩

def uncurry' (P Q R : Prop) (f : P → Q → R) (HPQ : P ∧ Q) : R :=
  match HPQ with
  | ⟨HP, HQ⟩ => f HP HQ

-- ------------------ PROOF IRRELEVANCE (ADVANCED) -----------------------

def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

theorem pe_implies_or_eq (PE : propositional_extensionality)
    (P Q : Prop) : (P ∨ Q) = (Q ∨ P) := by
  apply PE
  constructor
  · exact or_commut P Q
  · exact or_commut Q P

theorem pe_implies_true_eq (PE : propositional_extensionality)
    (P : Prop) (HP : P) : True = P := by
  apply PE
  constructor
  · intro _; exact HP
  · intro _; exact True.intro

def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2

theorem pe_implies_pi (PE : propositional_extensionality) : proof_irrelevance := by
  intro P pf1 pf2
  have H : P = True := by
    apply PE
    constructor
    · intro _; exact True.intro
    · intro _; exact pf1
  subst H
  cases pf1
  cases pf2
  rfl
