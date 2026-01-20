import Imp

-- ==================== LEXICAL ANALYSIS ====================

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

abbrev Token := String

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
