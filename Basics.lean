inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

#eval nextWorkingDay Day.friday
#eval nextWorkingDay (nextWorkingDay Day.saturday)

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

namespace MySpace

  inductive Bool where
    | true
    | false
  deriving Repr, DecidableEq

  def negb (b : Bool) : Bool :=
    match b with
    | Bool.true => Bool.false
    | Bool.false => Bool.true

  def andb (b1 : Bool) (b2 : Bool) : Bool :=
    match b1 with
    | Bool.true => b2
    | Bool.false => Bool.false

  def orb (b1 : Bool) (b2 : Bool) : Bool :=
    match b1 with
    | Bool.true => Bool.true
    | Bool.false => b2

  #eval negb Bool.true

  example : orb Bool.true Bool.false = Bool.true := by rfl
  example : orb Bool.false Bool.false = Bool.false := by rfl
  example : orb Bool.false Bool.true = Bool.true := by rfl
  example : orb Bool.true Bool.true = Bool.true := by rfl

  infixl:65 " && " => andb
  infixl:60 " || " => orb

  example : (Bool.true || (Bool.true || Bool.true)) = Bool.true := by rfl

  def negb' (b : Bool) : Bool :=
    if b = Bool.true then Bool.false else Bool.true

  inductive Bw where
    | black
    | white
  deriving Repr

  def invert (x : Bw) : Bw :=
    match x with
    | Bw.black => Bw.white
    | Bw.white => Bw.black

  #eval invert Bw.black
  #eval invert Bw.white

  inductive Bwr where
    | black
    | white
    | red
  deriving Repr

  def rotate (x : Bwr) : Bwr :=
    match x with
    | Bwr.black => Bwr.white
    | Bwr.white => Bwr.red
    | Bwr.red   => Bwr.black

  #eval rotate Bwr.white

  def nandb (b1 : Bool) (b2 : Bool) : Bool :=
    sorry

  example : nandb Bool.true Bool.false = Bool.true := by sorry
  example : nandb Bool.false Bool.false = Bool.true := by sorry
  example : nandb Bool.false Bool.true = Bool.true := by sorry
  example : nandb Bool.true Bool.true = Bool.false := by sorry

  def andb3 (b1 : Bool) (b2 : Bool) (b3 : Bool) : Bool :=
    sorry

  example : andb3 Bool.true Bool.true Bool.true = Bool.true := by sorry
  example : andb3 Bool.false Bool.true Bool.true = Bool.false := by sorry
  example : andb3 Bool.true Bool.false Bool.true = Bool.false := by sorry
  example : andb3 Bool.true Bool.true Bool.false = Bool.false := by sorry

end MySpace

#check MySpace.Bool.true
#check (MySpace.Bool.true : MySpace.Bool)

inductive Rgb where
  | red
  | green
  | blue
deriving Repr

inductive Color where
  | black
  | white
  | primary (p : Rgb)
deriving Repr

def monochrome (c : Color) : MySpace.Bool :=
  match c with
  | Color.black => MySpace.Bool.true
  | Color.white => MySpace.Bool.true
  | Color.primary _ => MySpace.Bool.false

def isred (c : Color) : MySpace.Bool :=
  match c with
  | Color.black => MySpace.Bool.false
  | Color.white => MySpace.Bool.false
  | Color.primary Rgb.red => MySpace.Bool.true
  | Color.primary _ => MySpace.Bool.false

namespace Playground
  def foo : Rgb := Rgb.blue
end Playground

def foo : MySpace.Bool := MySpace.Bool.true

#check Playground.foo
#check foo

namespace TuplePlayground

  inductive Bit where
    | B1
    | B0
  deriving Repr

  inductive Nybble where
    | bits (b0 b1 b2 b3 : Bit)
  deriving Repr

  #check (Nybble.bits Bit.B1 Bit.B0 Bit.B1 Bit.B0)

  def allZero (nb : Nybble) : MySpace.Bool :=
    match nb with
    | Nybble.bits Bit.B0 Bit.B0 Bit.B0 Bit.B0 => MySpace.Bool.true
    | Nybble.bits _ _ _ _ => MySpace.Bool.false

  #eval allZero (Nybble.bits Bit.B0 Bit.B0 Bit.B0 Bit.B0)

end TuplePlayground

namespace NatPlayground

  inductive Nat where
    | O
    | S (n : Nat)
  deriving Repr

  instance {n} : OfNat Nat n where
    ofNat :=
      let rec loop : _root_.Nat -> Nat
        | 0 => Nat.O
        | i + 1 => Nat.S (loop i)
      loop n

  def pred (n : Nat) : Nat :=
    match n with
    | Nat.O => Nat.O
    | Nat.S n' => n'

  def minustwo (n : Nat) : Nat :=
    match n with
    | Nat.O => Nat.O
    | Nat.S Nat.O => Nat.O
    | Nat.S (Nat.S n') => n'

  #eval minustwo 4

  def even (n : Nat) : MySpace.Bool :=
    match n with
    | Nat.O => MySpace.Bool.true
    | Nat.S Nat.O => MySpace.Bool.false
    | Nat.S (Nat.S n') => even n'

  def odd (n : Nat) : MySpace.Bool :=
    MySpace.negb (even n)

  example : odd 1 = MySpace.Bool.true := by rfl
  example : odd 4 = MySpace.Bool.false := by rfl

  def plus (n m : Nat) : Nat :=
    match n with
    | Nat.O => m
    | Nat.S n' => Nat.S (plus n' m)

  def mult (n m : Nat) : Nat :=
    match n with
    | Nat.O => Nat.O
    | Nat.S n' => plus m (mult n' m)

  def minus (n m : Nat) : Nat :=
    match n, m with
    | Nat.O, _ => Nat.O
    | Nat.S _, Nat.O => n
    | Nat.S n', Nat.S m' => minus n' m'

  def exp (base power : Nat) : Nat :=
    match power with
    | Nat.O => Nat.S Nat.O
    | Nat.S p => mult base (exp base p)

  example : (exp 2 3) = 8 := by rfl

  infixl:65 " + " => plus
  infixl:65 " - " => minus
  infixl:70 " * " => mult

  #eval (plus 3 2)

  def eqb (n m : Nat) : MySpace.Bool :=
    match n, m with
    | Nat.O,    Nat.O    => MySpace.Bool.true
    | Nat.O,    Nat.S _  => MySpace.Bool.false
    | Nat.S _,  Nat.O    => MySpace.Bool.false
    | Nat.S n', Nat.S m' => eqb n' m'

  def leb (n m : Nat) : MySpace.Bool :=
    match n with
    | Nat.O => MySpace.Bool.true
    | Nat.S n' =>
        match m with
        | Nat.O => MySpace.Bool.false
        | Nat.S m' => leb n' m'

  def lb (n m : Nat) : MySpace.Bool :=
    match n, m with
    | Nat.O, Nat.O => MySpace.Bool.false
    | Nat.O, Nat.S _ => MySpace.Bool.true
    | Nat.S _, Nat.O => MySpace.Bool.false
    | Nat.S n', Nat.S m' => lb n' m'

  infix:50 " =? " => eqb
  infix:70 " <=? " => leb

  example : 5 <=? 4 = MySpace.Bool.false := by rfl

  def factorial (n : Nat) : Nat :=
    sorry

  example : factorial 3 = 6 := by sorry

  def ltb (n m : Nat) : MySpace.Bool :=
    sorry

  infix:70 " <? " => ltb

  example : (ltb 2 2) = MySpace.Bool.false := by sorry
  example : (ltb 2 4) = MySpace.Bool.true := by sorry
  example : (ltb 4 2) = MySpace.Bool.false := by sorry


end NatPlayground



