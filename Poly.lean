-- import Lists
namespace Poly

-- POLYMORPHIC LISTS

inductive BoolList : Type where
  | bool_nil
  | bool_cons (b: Bool) (l : BoolList)

inductive List (X : Type) : Type where
  | nil
  | cons (x : X)(l : List X)
  deriving Repr

#check List
#check @List.nil Nat
#check (@List.cons Nat 3 (@List.nil Nat))
#check (@List.cons Nat 3 (@List.cons Nat 2 (@List.cons Nat 1 (@List.nil Nat))))
#check @List.nil
#check @List.cons


-- Polymorphic versions of Lists functions
def repeatN (X:Type) (x : X) (count : Nat) : List X :=
  match count with
  | 0 => @List.nil X
  | .succ count' => @List.cons X x (repeatN X x count')

example : repeatN Nat 4 2 = @List.cons Nat 4 (@List.cons Nat 4 (@List.nil Nat)) := by
  rfl
example : repeatN Bool false 1 = @List.cons Bool false (@List.nil Bool) := by
  rfl

namespace MumbleGrumble

  inductive Mumble : Type where
    | a
    | b (x : Mumble) (y : Nat)
    | c

  inductive Grumble (X : Type) : Type where
    | d (m : Mumble)
    | e (x : X)

end MumbleGrumble

-- (* Type Annotation Inference *)

-- Lean inference is very strong.
-- Even without explicit types, it usually finds them.
def repeatN' (X : Type) (x : X) (count : Nat) : List X :=
  match count with
  | 0 => List.nil -- Lean infers (List.nil : List X)
  | Nat.succ count' => List.cons x (repeatN' X x count')

#check repeatN'
#check repeatN

def repeatN'' (X : Type) (x : X) (count : Nat) : List X :=
  match count with
  | 0 => @List.nil _
  | Nat.succ count' => @List.cons _ x (repeatN'' _ x count')

def list123' :=
  @List.cons _ 1 (@List.cons _ 2 (@List.cons _ 3 (@List.nil _)))


-- (* Implicit Arguments *)

-- In Coq: Arguments nil {X}.
-- In Lean, we typically define the function with braces {X : Type}
-- to make it implicit at the definition site.

def list123'' := List.cons 1 (List.cons 2 (List.cons 3 List.nil))

-- Notice {X : Type} in the binder
def repeat''' {X : Type} (x : X) (count : Nat) : List X :=
  match count with
  | 0 => .nil
  | .succ count' => List.cons x (repeat''' x count')

-- The app function (append)
def app {X : Type} (l1 l2 : List X) : List X :=
  match l1 with
  | .nil => l2
  | .cons h t => List.cons h (app t l2)

def rev {X: Type} (l : List X) : List X :=
  match l with
  | .nil => .nil
  | .cons h t => app (rev t) (.cons h .nil)

def length {X : Type} (l : List X) : Nat :=
  match l with
  | .nil => 0
  | .cons _ l' => Nat.succ (length l')


example : rev (List.cons 1 (List.cons 2 List.nil)) =
          (List.cons 2 (List.cons 1 List.nil)) := by rfl
example : rev (List.cons true List.nil) = List.cons true List.nil := by rfl
example : length (List.cons 1 (List.cons 2 (List.cons 3 List.nil))) = 3 := by rfl

-- (* Supplying Type Arguments Explicitly *)

def mynil : List Nat := List.nil

-- Using @ to provide the type argument explicitly
#check @List.nil
def mynil' := @List.nil Nat

-- (* Notation *)

-- We define local notation to match Coq's syntax.
-- We use a high precedence for :: and ++.
infixr:67 " :: " => List.cons
notation "[]" => List.nil
infixr:60 " ++ " => app

-- Custom syntax for [x, y, z] literals for our custom List
syntax (name := polyList) (priority := 1000) "[" term,* "]" : term
macro_rules (kind := polyList)
  | `([ ]) => `(List.nil)
  | `([ $x ]) => `(List.cons $x List.nil)
  | `([ $x, $xs,* ]) => `(List.cons $x [$xs,*])

-- (* Theorems *)

theorem app_nil_r : ∀ (X : Type) (l : List X),
  l ++ [] = l := by
  intro X l
  induction l with
  | nil => rfl
  | cons n l' ih =>
    simp [app] -- Expands definitions
    rw [ih]

theorem app_assoc : ∀ A (l m n : List A),
  l ++ m ++ n = (l ++ m) ++ n := by
  intro A l m n
  induction l with
  | nil => rfl
  | cons h l' ih =>
    simp [app]
    rw [ih]

theorem app_length : ∀ (X : Type) (l1 l2 : List X),
  length (l1 ++ l2) = length l1 + length l2 := by
  intro X l1 l2
  induction l1 with
  | nil => simp[length]
           rfl
  | cons n l' ih =>
    simp [length, app]
    rw [ih]
    -- We need associativity of Nat addition (sometimes simp handles this automatically)
    simp [Nat.add_comm, Nat.add_left_comm]

theorem rev_app_distr : ∀ X (l1 l2 : List X),
  rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  intro X l1 l2
  induction l1 with
  | nil =>
    simp [rev, app]
    rw [app_nil_r]
  | cons x l1' ih =>
    simp [rev, app]
    rw [ih]
    rw [app_assoc]

theorem rev_involutive : ∀ X (l : List X),
  rev (rev l) = l := by
  intro X l
  induction l with
  | nil => rfl
  | cons x l' ih =>
    simp [rev]
    rw [rev_app_distr]
    simp [rev]
    rw [ih]
    rfl

-- (* ------ Polymorphic Pairs -------- *)

inductive Prod (X Y : Type) : Type where
  | pair (x : X) (y : Y)
  deriving Repr

-- Notation setup to match Coq
-- We use a specific precedence to avoid conflict with standard multiplication
infixr:35 " * " => Prod
notation "(" x "," y ")" => Prod.pair x y

-- Implicit arguments for pair are handled automatically by Lean if we don't specify them,
-- but we can verify check:
#check @Prod.pair

def fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x

def snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y

-- combining two lists into a list of pairs (zip)
def combine {X Y : Type} (lx : List X) (ly : List Y) : List (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)

-- Compute example
-- Note: We use our custom list notation
#eval combine [1, 2] [false, false, true, true]
-- Result: [(1, false), (2, false)]


def split {X Y : Type} (l : List (X * Y)) : (List X) * (List Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (xs, ys) := split t
    (x :: xs, y :: ys)

example :
  split (X := Nat) (Y := Bool)
    (List.cons (Prod.pair (X := Nat) (Y := Bool) 1 false)
      (List.cons (Prod.pair (X := Nat) (Y := Bool) 2 false)
        (List.nil)))
  =
  Prod.pair
    (List.cons 1 (List.cons 2 (List.nil)))
    (List.cons false (List.cons false (List.nil))) := by
  rfl


-- (* Polymorphic Options *)

namespace OptionPlayground

  inductive Option (X : Type) : Type where
    | Some (x : X)
    | None
    deriving Repr

  -- In Lean, constructors are namespaced.
  -- We can 'export' them if we want to use Some/None directly.
  export Option (Some None)

end OptionPlayground

-- We export it to the outer Poly namespace too so we can use it below
export OptionPlayground (Option Some None)


def nth_error {X : Type} (l : List X) (n : Nat) : Option X :=
  match l with
  | [] => None
  | a :: l' =>
    match n with
    | 0 => Some a
    | Nat.succ n' => nth_error l' n'

example  : nth_error [4, 5, 6, 7] 0 = Some 4 := by rfl

-- Note: In Lean, [[1], [2]] syntax works with our macro rules from previous section
example :
  nth_error
    (List.cons (List.cons 1 (List.nil))
      (List.cons (List.cons 2 (List.nil)) (List.nil)))
    1
  =
  Some (List.cons 2 (List.nil)) := by
  rfl


example  : nth_error [true] 2 = None := by rfl


def hd_error {X : Type} (l : List X) : Option X :=
  match l with
  | [] => None
  | a :: _ => Some a

#check @hd_error
-- Output: @hd_error : {X : Type} → List X → Option X

example  : hd_error [1, 2] = Some 1 := by rfl

example :
  hd_error
    (List.cons (List.cons 1 (List.nil))
      (List.cons (List.cons 2 (List.nil)) (List.nil)))
  =
  Some (List.cons 1 (List.nil)) := by
  rfl

-- Helpers for the examples to work
def minustwo (n : Nat) : Nat := n - 2
def even (n : Nat) : Bool := n % 2 == 0
def odd (n : Nat) : Bool := n % 2 != 0

-- (* -------- FUNCTIONS AS DATA ------------ *)

def doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

#check @doit3times
-- Output: @doit3times : {X : Type} → (X → X) → X → X

example  : doit3times minustwo 9 = 3 := by rfl
example  : !true = false := by rfl

def filter {X : Type} (test : X → Bool) (l : List X) : List X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t

abbrev LNat   := List Nat
abbrev LBool  := List Bool
abbrev LLNat  := List (List Nat)
abbrev LLBool := List (List Bool)

example  :
  filter even ([1, 2, 3, 4] : LNat) = ([2, 4] : LNat) := by
  rfl
def length_is_1 {X : Type} (l : List X) : Bool :=
  (length l) == 1

example :
  filter length_is_1
    ([ [1, 2], [3], [4], [5, 6, 7], [], [8] ] : LLNat)
  =
    ([ [3], [4], [8] ] : LLNat) := by
  rfl

def countoddmembers' (l : List Nat) : Nat :=
  length (filter odd l)

example  : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by rfl
example  : countoddmembers' [0, 2, 4] = 0 := by rfl
example  : countoddmembers' [] = 0 := by rfl

-- (* Anonymous Functions *)

example  : doit3times (fun n => n * n) 2 = 256 := by rfl

example :
  filter (fun l => (length l) == 1)
    ([ [1, 2], [3], [4], [5, 6, 7], [], [8] ] : LLNat)
  =
    ([ [3], [4], [8] ] : LLNat) := by
  rfl

def filter_even_gt7 (l : List Nat) : List Nat :=
  filter (fun n => (even n) && (8 <= n)) l

example :
  filter_even_gt7 ([1, 2, 6, 9, 10, 3, 12, 8] : LNat) = ([10, 12, 8] : LNat) := by
  rfl

example  :
  filter_even_gt7 [5, 2, 6, 19, 129] = [] := by rfl

-- Note: We return a Prod (List X * List X)
def partition {X : Type} (test : X → Bool) (l : List X) : List X * List X :=
  (filter test l, filter (fun x => !(test x)) l)

example :
  partition odd ([1, 2, 3, 4, 5] : LNat)
    = Prod.pair ([1, 3, 5] : LNat) ([2, 4] : LNat) := by
  rfl

example :
  partition (fun _ => false) ([5, 9, 0] : LNat)
    = Prod.pair ([] : LNat) ([5, 9, 0] : LNat) := by
  rfl



def map {X Y : Type} (f : X → Y) (l : List X) : List Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)

example :
  map (fun x => 3 + x) ([2, 0, 2] : LNat) = ([5, 3, 5] : LNat) := by
  rfl

example  :
  map odd ([2, 1, 2, 5] : LNat) = ([false, true, false, true] : LBool) := by
  rfl

example :
  map (fun n => ([even n, odd n] : LBool)) ([2, 1, 2, 5] : LNat)
    = ([[true, false], [false, true], [true, false], [false, true]] : LLBool) := by
  rfl

theorem map_app : ∀ (X Y : Type) (f : X → Y) (l1 l2 : List X),
  map f (l1 ++ l2) = map f l1 ++ map f l2 := by
  intro X Y f l1 l2
  induction l1 with
  | nil => rfl
  | cons x l1' ih =>
    simp [map, app]
    rw [ih]

theorem map_rev : ∀ (X Y : Type) (f : X → Y) (l : List X),
  map f (rev l) = rev (map f l) := by
  intro X Y f l
  induction l with
  | nil => rfl
  | cons x l' ih =>
    simp [rev, map]
    rw [map_app]
    rw [ih]
    rfl

def flat_map {X Y : Type} (f : X → List Y) (l : List X) : List Y :=
  match l with
  | [] => []
  | h :: t => app (f h) (flat_map f t)

example :
  flat_map (fun n => ([n, n, n] : LNat)) ([1, 5, 4] : LNat)
  = ([1, 1, 1, 5, 5, 5, 4, 4, 4] : LNat) := by
  rfl


-- (* Map for Options *)

def option_map {X Y : Type} (f : X → Y) (xo : Option X) : Option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
-- (* Fold *)

def fold {X Y : Type} (f : X → Y → Y) (l : List X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

#check (fold (fun x y => x && y)) -- Lean infers types correctly

example :
  fold (fun x y => x && y) [true, true, false, true] true = false := by rfl

example :
  fold (fun x y => x * y) [1, 2, 3, 4] 1 = 24 := by rfl

example :
  fold app ([ [1], [], [2, 3], [4] ] : LLNat) ([] : LNat) = ([1, 2, 3, 4] : LNat) := by
  rfl

example :
  fold (fun l n => length l + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl

-- (* Functions that construct Functions *)

def constfun {X : Type} (x : X) : Nat → X :=
  fun (_ : Nat) => x

def ftrue := constfun true
#check ftrue


example : ftrue 0 = true := by rfl

#check (constfun ([5] : LNat))

example : (constfun 5) 99 = 5 := by rfl


-- (* plus3 *)
-- 'Nat.add' is the Lean equivalent of 'plus'
#check Nat.add

def plus3 := Nat.add 3
#check plus3


example : plus3 4 = 7 := by rfl
example : doit3times plus3 0 = 9 := by rfl

-- (* ADDITIONAL EXERCISES *)

namespace Exercises

  def fold_length {X : Type} (l : List X) : Nat :=
    Poly.fold (fun _ n => Nat.succ n) l 0

  example : fold_length ([4, 7, 0] : LNat) = 3 := by rfl

  theorem fold_length_correct : ∀ (X : Type) (l : List X),
    fold_length l = Poly.length l := by
    intro X l
    induction l with
    | nil => rfl
    | cons n l' ih =>
      simp [fold_length, Poly.fold, Poly.length]
      rw [← ih] -- rewriting backwards using the inductive hypothesis
      rfl

  def fold_map {X Y : Type} (f : X → Y) (l : List X) : List Y :=
    Poly.fold (fun x r => List.cons (f x) r) l List.nil

  theorem fold_map_correct : ∀ {X Y : Type} (f : X → Y) (l : List X),
    Poly.map f l = fold_map f l := by
    intro X Y f l
    induction l with
    | nil => rfl
    | cons n l' ih =>
      simp [Poly.map, fold_map, Poly.fold]
      rw [ih]
      rfl

  def prod_curry {X Y Z : Type}
    (f : Poly.Prod X Y → Z) (x : X) (y : Y) : Z :=
    f (Poly.Prod.pair x y)

  def prod_uncurry {X Y Z : Type}
    (f : X → Y → Z) (p : Poly.Prod X Y) : Z :=
    match p with
    | Poly.Prod.pair x y => f x y

  theorem uncurry_curry : ∀ (X Y Z : Type) (f : X → Y → Z) (x : X) (y : Y),
    prod_curry (prod_uncurry f) x y = f x y := by
    intro X Y Z f x y
    rfl

  theorem curry_uncurry : ∀ (X Y Z : Type) (f : Poly.Prod X Y → Z) (p : Poly.Prod X Y),
    prod_uncurry (prod_curry f) p = f p := by
    intro X Y Z f p
    cases p with
    | pair x y => rfl

end Exercises

namespace Church

  def cnat := ∀ (X : Type), (X → X) → X → X

  def one : cnat :=
    fun (X : Type) (f : X → X) (x : X) => f x

  #check one

  def two : cnat :=
    fun (X : Type) (f : X → X) (x : X) => f (f x)

  def zero : cnat :=
    fun (X : Type) (_ : X → X) (x : X) => x

  -- Note: @doit3times makes the implicit type argument explicit, matching cnat
  def three : cnat := @doit3times

  -- Alternative definitions with explicit names
  def zero' : cnat :=
    fun (X : Type) (_ : X → X) (zero : X) => zero

  def one' : cnat :=
    fun (X : Type) (succ : X → X) (zero : X) => succ zero

  def two' : cnat :=
    fun (X : Type) (succ : X → X) (zero : X) => succ (succ zero)

  -- Peano examples
  example : zero Nat Nat.succ 0 = 0 := by rfl
  example : one Nat Nat.succ 0 = 1 := by rfl
  example : two Nat Nat.succ 0 = 2 := by rfl


  def scc (n : cnat) : cnat :=
    fun (X : Type) (f : X → X) (x : X) => f (n X f x)

  -- In Lean, rfl works here because these beta-reduce to identical terms
  example : scc zero = one := by rfl
  example : scc one = two := by rfl
  example : scc two = three := by rfl

  def plus (n m : cnat) : cnat :=
    fun (X : Type) (f : X → X) (x : X) => n X f (m X f x)

  example : plus zero one = one := by rfl
  example : plus two three = plus three two := by rfl

  example :
    plus (plus two two) three = plus one (plus three three) := by rfl

  def mult (n m : cnat) : cnat :=
    fun (X : Type) (f : X → X) (x : X) => n X (m X f) x

  example : mult one one = one := by rfl
  example : mult zero (plus three three) = zero := by rfl
  example : mult two three = plus three three := by rfl

  -- Exponentiation (n^m)
  def exp (n m : cnat) : cnat :=
    fun (X : Type) (f : X → X) (x : X) => (m (X → X) (n X)) f x

  example : exp two two = plus two two := by rfl
  example : exp three zero = one := by rfl
  example : exp three two = plus (mult two (mult two two)) one := by rfl

end Church

end Poly
