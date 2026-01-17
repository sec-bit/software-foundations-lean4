-- ------------------ ARITHMETIC AND BOOLEAN EXPRESSIONS -----------------------

-- Arithmetic expressions
inductive AExp : Type where
  | ANum (n : Nat)
  | APlus (a1 a2 : AExp)
  | AMinus (a1 a2 : AExp)
  | AMult (a1 a2 : AExp)

-- Boolean expressions
inductive BExp : Type where
  | BTrue
  | BFalse
  | BEq (a1 a2 : AExp)
  | BNeq (a1 a2 : AExp)
  | BLe (a1 a2 : AExp)
  | BGt (a1 a2 : AExp)
  | BNot (b : BExp)
  | BAnd (b1 b2 : BExp)

open AExp BExp

-- ------------------ EVALUATION -----------------------

-- Evaluate arithmetic expression to Nat
def aeval (a : AExp) : Nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  | AMult a1 a2 => aeval a1 * aeval a2

example : aeval (APlus (ANum 2) (ANum 2)) = 4 := rfl

-- Evaluate boolean expression to Bool
-- Coq: =? is Nat.eqb, <=? is Nat.leb, negb is !, andb is &&
def beval (b : BExp) : Bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BExp.BEq a1 a2 => aeval a1 == aeval a2
  | BNeq a1 a2 => !(aeval a1 == aeval a2)
  | BLe a1 a2 => aeval a1 ≤ aeval a2   -- Nat has Decidable LE, returns Bool in this context
  | BGt a1 a2 => !(aeval a1 ≤ aeval a2)
  | BNot b1 => !beval b1
  | BAnd b1 b2 => beval b1 && beval b2

-- ------------------ OPTIMIZATION -----------------------

-- Remove 0 + e, replacing with just e
def optimize_0plus (a : AExp) : AExp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)

example : optimize_0plus (APlus (ANum 2)
                           (APlus (ANum 0)
                             (APlus (ANum 0) (ANum 1))))
          = APlus (ANum 2) (ANum 1) := rfl

theorem optimize_0plus_sound (a : AExp) : aeval (optimize_0plus a) = aeval a := by
  induction a with
  | ANum n => rfl
  | APlus a1 a2 IHa1 IHa2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero => simp_all [optimize_0plus, aeval]
      | succ n => simp_all [optimize_0plus, aeval]
    | APlus _ _ => simp_all [optimize_0plus, aeval]
    | AMinus _ _ => simp_all [optimize_0plus, aeval]
    | AMult _ _ => simp_all [optimize_0plus, aeval]
  | AMinus a1 a2 IHa1 IHa2 => simp_all [optimize_0plus, aeval]
  | AMult a1 a2 IHa1 IHa2 => simp_all [optimize_0plus, aeval]
