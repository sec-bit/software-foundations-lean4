import Imp
deriving instance Repr for AExp'
-- --------------------- LEXICAL ANALYSIS ---------------------

def isWhite (c : Char) : Bool :=
  let n := c.toNat
  n == 32 || n == 9 || n == 10 || n == 13  -- space, tab, LF, CR

def isLowerAlpha (c : Char) : Bool :=
  let n := c.toNat
  97 ≤ n && n ≤ 122  -- 'a' to 'z'

def isAlpha (c : Char) : Bool :=
  let n := c.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)  -- A-Z or a-z

def isDigit (c : Char) : Bool :=
  let n := c.toNat
  48 ≤ n && n ≤ 57  -- '0' to '9'

inductive CharType where
  | white
  | alpha
  | digit
  | other
  deriving Repr, BEq

def classifyChar (c : Char) : CharType :=
  if isWhite c then .white
  else if isAlpha c then .alpha
  else if isDigit c then .digit
  else .other

-- Lean's String.toList and String.mk replace list_of_string/string_of_list

def Token := String

-- tokenize_helper is not structurally recursive on any argument
-- Lean can't prove termination, so we use `partial`
partial def tokenizeHelper (cls : CharType) (acc xs : List Char) : List (List Char) :=
  let tk := if acc.isEmpty then [] else [acc.reverse]
  match xs with
  | [] => tk
  | x :: xs' =>
    match cls, classifyChar x, x with
    | _, _, '(' => tk ++ [['(']] ++ tokenizeHelper .other [] xs'
    | _, _, ')' => tk ++ [[')']] ++ tokenizeHelper .other [] xs'
    | _, .white, _ => tk ++ tokenizeHelper .white [] xs'
    | .alpha, .alpha, _ => tokenizeHelper .alpha (x :: acc) xs'
    | .digit, .digit, _ => tokenizeHelper .digit (x :: acc) xs'
    | .other, .other, _ => tokenizeHelper .other (x :: acc) xs'
    | _, tp, _ => tk ++ tokenizeHelper tp [x] xs'

def tokenize (s : String) : List String :=
  (tokenizeHelper .white [] s.toList).map String.mk

-- Test
#eval tokenize "abc12=3  223*(3+(a+c))"
-- Expected: ["abc", "12", "=", "3", "223", "*", "(", "3", "+", "(", "a", "+", "c", ")", ")"]

-- ------------------- OPTIONS WITH ERRORS -------------------

inductive OptionE (α : Type) where
  | SomeE (x : α)
  | NoneE (err : String)
  deriving Repr

-- Monad instance gives us `do` notation
instance : Monad OptionE where
  pure x := .SomeE x
  bind e f := match e with
    | .SomeE x => f x
    | .NoneE err => .NoneE err

-- OrElse instance gives us `<|>` (replaces TRY...OR)
instance : OrElse (OptionE α) where
  orElse e1 e2 := match e1 with
    | .SomeE x => .SomeE x
    | .NoneE _ => e2 ()  -- e2 is thunked: Unit → OptionE α

-- ------------------- GENERIC PARSER COMBINATORS -------------------

def Parser (α : Type) := List Token → OptionE (α × List Token)

-- ------------------- GENERIC PARSER COMBINATORS -------------------

-- Required for partial definitions
instance : Inhabited (OptionE α) where
  default := .NoneE "default"

def manyHelper {α : Type} (p : Parser α) (acc : List α) (steps : Nat) (xs : List Token) : OptionE (List α × List Token) :=
  match steps, p xs with
  | 0, _ => .NoneE "Too many recursive calls"
  | _, .NoneE _ => .SomeE (acc.reverse, xs)
  | .succ steps', .SomeE (t, xs') => manyHelper p (t :: acc) steps' xs'

def many {α : Type} (p : Parser α) (steps : Nat) : Parser (List α) :=
  manyHelper p [] steps

-- def firstExpect {α : Type} (t : String) (p : Parser α) : Parser α := fun xs =>
--   match xs with
--   | x :: xs' =>
--     if (x : String) == t then p xs'
--     else .NoneE ("expected '" ++ t ++ "'." : String)
--   | [] => .NoneE ("expected '" ++ t ++ "'." : String)

-- def expect (t : Token) : Parser Unit :=
--   firstExpect t (fun xs => .SomeE ((), xs))

-- ------------------- RECURSIVE-DESCENT PARSER -------------------

-- Identifiers
def parseIdentifier (xs : List Token) : OptionE (String × List Token) :=
  match xs with
  | [] => .NoneE "Expected identifier"
  | x :: xs' =>
    if x.toList.all isLowerAlpha then .SomeE (x, xs')
    else .NoneE "Expected Identifier"

-- Numbers
def parseNumber (xs : List Token) : OptionE (Nat × List Token) :=
  match xs with
  | [] => .NoneE "Expected number"
  | x :: xs' =>
    if x.toList.all isDigit then
      let n := x.toList.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0
      .SomeE (n, xs')
    else .NoneE "Expected number"

-- ------------------- ARITHMETIC EXPRESSIONS -------------------

-- mutual
--   partial def parsePrimaryExp (steps : Nat) (xs : List Token) : OptionE (AExp' × List Token) :=
--     match steps with
--     | 0 => .NoneE "Too many recursive calls"
--     | .succ steps' =>
--       (do let (i, rest) ← parseIdentifier xs
--           pure (AExp'.AId i, rest))
--       <|>
--       (do let (n, rest) ← parseNumber xs
--           pure (AExp'.ANum n, rest))
--       <|>
--       (do let (e, rest) ← firstExpect "(" (parseSumExp steps') xs
--           let (_, rest') ← expect ")" rest
--           pure (e, rest'))

--   partial def parseProductExp (steps : Nat) (xs : List Token) : OptionE (AExp' × List Token) :=
--     match steps with
--     | 0 => .NoneE "Too many recursive calls"
--     | .succ steps' => do
--       let (e, rest) ← parsePrimaryExp steps' xs
--       let (es, rest') ← many (firstExpect "*" (parsePrimaryExp steps')) steps' rest
--       pure (es.foldl AExp'.AMult e, rest')

--   partial def parseSumExp (steps : Nat) (xs : List Token) : OptionE (AExp' × List Token) :=
--     match steps with
--     | 0 => .NoneE "Too many recursive calls"
--     | .succ steps' => do
--       let (e, rest) ← parseProductExp steps' xs
--       let (es, rest') ← many (fun xs =>
--           (do let (e, rest') ← firstExpect "+" (parseProductExp steps') xs
--               pure ((true, e), rest'))
--           <|>
--           (do let (e, rest') ← firstExpect "-" (parseProductExp steps') xs
--               pure ((false, e), rest')))
--         steps' rest
--       pure (es.foldl (fun e0 term =>
--           match term with
--           | (true, e) => AExp'.APlus e0 e
--           | (false, e) => AExp'.AMinus e0 e) e, rest')
-- end

-- def parseAExp := parseSumExp
-- deriving instance Repr for AExp'
-- Test
-- #eval parseAExp 100 (tokenize "3+4*5")
