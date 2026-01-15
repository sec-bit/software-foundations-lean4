-- ----------------------- Maps: Total and Partial Maps ---------------------

/-
  Coq uses String.eqb (boolean equality) with reflection lemmas:
    String.eqb_refl : ∀ x, (x =? x) = true
    String.eqb_eq   : (n =? m) = true ↔ n = m
    String.eqb_neq  : (n =? m) = false ↔ n ≠ m
    String.eqb_spec : reflect (x = y) (String.eqb x y)

  Lean uses DecidableEq: `if x = y then ... else ...`
  with proof terms available in each branch.
  Coq's `destruct (eqb_spec x y)` becomes `by_cases h : x = y`.
-/

-- ----------------------- TOTAL MAPS -----------------------

def TotalMap (A : Type) := String → A

def tEmpty {A : Type} (v : A) : TotalMap A :=
  fun _ => v

/--
  Coq: if String.eqb x x' then v else m x'
  Lean: if x = x' then v else m x'

  Uses DecidableEq instance for String.
-/
def tUpdate {A : Type} (m : TotalMap A) (x : String) (v : A) : TotalMap A :=
  fun x' => if x = x' then v else m x'

/-
  Coq defines notations:
    Notation "'_' '!->' v" := (t_empty v)
    Notation "x '!->' v ';' m" := (t_update m x v)

  We use plain function application for clarity.
-/
def exampleMap : TotalMap Bool :=
  tUpdate (tUpdate (tEmpty false) "foo" true) "bar" true

example : exampleMap "baz" = false := rfl
example : exampleMap "foo" = true := rfl
example : exampleMap "quux" = false := rfl
example : exampleMap "bar" = true := rfl

theorem tApply_empty {A : Type} (x : String) (v : A) :
    tEmpty v x = v := rfl

theorem tUpdate_eq {A : Type} (m : TotalMap A) (x : String) (v : A) :
    tUpdate m x v x = v := by
  simp [tUpdate]

theorem tUpdate_neq {A : Type} (m : TotalMap A) (x1 x2 : String) (v : A)
    (h : x1 ≠ x2) : tUpdate m x1 v x2 = m x2 := by
  simp [tUpdate, h]

theorem tUpdate_shadow {A : Type} (m : TotalMap A) (x : String) (v1 v2 : A) :
    tUpdate (tUpdate m x v1) x v2 = tUpdate m x v2 := by
  funext x'
  simp only [tUpdate]
  by_cases h : x = x' <;> simp [h]

theorem tUpdate_same {A : Type} (m : TotalMap A) (x : String) :
    tUpdate m x (m x) = m := by
  funext x'
  simp [tUpdate]
  intro h
  rw [h]

theorem tUpdate_permute {A : Type} (m : TotalMap A) (v1 v2 : A) (x1 x2 : String)
    (h : x2 ≠ x1) : tUpdate (tUpdate m x2 v2) x1 v1 = tUpdate (tUpdate m x1 v1) x2 v2 := by
  funext x'
  simp [tUpdate]
  by_cases h1 : x1 = x'
  · by_cases h2 : x2 = x'
    · -- x1 = x' and x2 = x' implies x1 = x2, contradicting h
      exact absurd (h2.trans h1.symm) h
    · simp [h1, h2]
  · by_cases h2 : x2 = x' <;> simp [h1, h2]

-- ----------------------- PARTIAL MAPS -----------------------

def PartialMap (A : Type) := TotalMap (Option A)

def emptyMap {A : Type} : PartialMap A := tEmpty none

def update {A : Type} (m : PartialMap A) (x : String) (v : A) : PartialMap A :=
  tUpdate m x (some v)

def examplePMap : PartialMap Bool :=
  update (update emptyMap "Turing" false) "Church" true

theorem apply_empty {A : Type} (x : String) :
    @emptyMap A x = none := rfl

theorem update_eq {A : Type} (m : PartialMap A) (x : String) (v : A) :
    update m x v x = some v := tUpdate_eq m x (some v)

theorem update_neq {A : Type} (m : PartialMap A) (x1 x2 : String) (v : A)
    (h : x2 ≠ x1) : update m x2 v x1 = m x1 := tUpdate_neq m x2 x1 (some v) h

theorem update_shadow {A : Type} (m : PartialMap A) (x : String) (v1 v2 : A) :
    update (update m x v1) x v2 = update m x v2 := tUpdate_shadow m x (some v1) (some v2)

theorem update_same {A : Type} (m : PartialMap A) (x : String) (v : A)
    (h : m x = some v) : update m x v = m := by
  unfold update
  rw [← h]
  exact tUpdate_same m x

theorem update_permute {A : Type} (m : PartialMap A) (x1 x2 : String) (v1 v2 : A)
    (h : x2 ≠ x1) : update (update m x2 v2) x1 v1 = update (update m x1 v1) x2 v2 :=
  tUpdate_permute m (some v1) (some v2) x1 x2 h

def includedIn {A : Type} (m m' : PartialMap A) : Prop :=
  ∀ x v, m x = some v → m' x = some v

theorem includedIn_update {A : Type} (m m' : PartialMap A) (x : String) (vx : A)
    (h : includedIn m m') : includedIn (update m x vx) (update m' x vx) := by
  intro y vy
  by_cases hxy : x = y
  · rw [hxy, update_eq, update_eq]
    exact id
  · rw [update_neq m y x vx hxy, update_neq m' y x vx hxy]
    exact h y vy
