-- α is an implicit type parameter.
-- x has type α.
-- The result is a List containing elements of type α.
def repeatN {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0 => []
  | Nat.succ count' => x :: (repeatN x count')

-- Lean infers α is Nat because 4 is a Nat
#eval repeatN 4 2
-- Result: [4, 4]

-- Lean infers α is Bool because false is a Bool
#eval repeatN false 2
-- Result: [false, false]

theorem app_nil_r {α : Type} (l : List α) : l ++ [] = l := by
  /- FILL IN HERE -/ sorry

theorem app_assoc {α : Type} (l m n : List α) : l ++ m ++ n = l ++ (m ++ n) := by
  /- FILL IN HERE -/ sorry

theorem app_length {α : Type} (l1 l2 : List α) :
  (l1 ++ l2).length = l1.length + l2.length := by
  /- FILL IN HERE -/ sorry

def myPair : Nat × Bool := (3, true)

#check myPair
-- Result: myPair : Nat × Bool

def combine {α β : Type} (l1 : List α) (l2 : List β) : List (α × β) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty

def split {α β : Type} (l : List (α × β)) : (List α) × (List β) :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : split [(1, false), (2, false)] = ([1, 2], [false, false]) := by
  /- FILL IN HERE -/ sorry


def nth_error {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' =>
    match n with
    | 0 => some a
    | Nat.succ n' => nth_error l' n'

example : nth_error [4, 5, 6, 7] 0 = some 4 := rfl
example : nth_error [true] 2 = none := rfl

def hd_error {α : Type} (l : List α) : Option α :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : hd_error [1, 2] = some 1 := by
  /- FILL IN HERE -/ sorry

example : hd_error (α := Nat) [] = none := by
  /- FILL IN HERE -/ sorry

def doit3times {α : Type} (f : α -> α) (n : α) : α :=
  f (f (f n))

def minustwo (n : Nat) : Nat := n - 2

example : doit3times minustwo 9 = 3 := rfl

def filter {α : Type} (test : α -> Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t

-- Keep only even numbers
example : filter (fun x => x % 2 == 0) [1, 2, 3, 4] = [2, 4] := rfl

def filter_even_gt7 (l : List Nat) : List Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : filter_even_gt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := by
  /- FILL IN HERE -/ sorry

def partition {α : Type} (test : α -> Bool) (l : List α) : List α × List α :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : partition (fun x => x % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := by
  /- FILL IN HERE -/ sorry

def map {α β : Type} (f : α -> β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)

example : map (fun x => x + 3) [2, 0, 2] = [5, 3, 5] := rfl

theorem map_rev {α β : Type} (f : α -> β) (l : List α) :
  map f (l.reverse) = (map f l).reverse := by
  /- FILL IN HERE -/ sorry

def flat_map {α β : Type} (f : α -> List β) (l : List α) : List β :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : flat_map (fun n => [n, n+1, n+2]) [1, 5, 10]
  = [1, 2, 3, 5, 6, 7, 10, 11, 12] := by
  /- FILL IN HERE -/ sorry

def fold {α β : Type} (f : α -> β -> β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

-- Example: Sum of list
-- fold (+) [1, 2, 3, 4] 0  ==>  1 + (2 + (3 + (4 + 0)))
example : fold Nat.add [1, 2, 3, 4] 0 = 10 := rfl

def fold_length {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

theorem fold_length_correct {α : Type} (l : List α) :
  fold_length l = l.length := by
  /- FILL IN HERE -/ sorry

def prod_curry {α β γ : Type}
  (f : α × β -> γ) (x : α) (y : β) : γ := f (x, y)

def prod_uncurry {α β γ : Type}
  (f : α -> β -> γ) (p : α × β) : γ :=
  f p.1 p.2

theorem uncurry_curry {α β γ : Type}
  (f : α -> β -> γ) (x : α) (y : β) :
  prod_curry (prod_uncurry f) x y = f x y := by
  /- FILL IN HERE -/ sorry

theorem curry_uncurry {α β γ : Type}
  (f : (α × β) -> γ) (p : α × β) :
  prod_uncurry (prod_curry f) p = f p := by
  /- FILL IN HERE -/ sorry
