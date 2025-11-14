import Pizza.Language
import Pizza.Parser

def perens (op : Char) : Option (Char → Bool) :=
  match op with
  | '(' => some (λ r => r == ')')
  | _   => none

def infixOp (op : Char) : Option (Nat × Nat) :=
  match op with
  | '+' | '-' => some (1, 2)
  | '*' | '/' => some (3, 4)
  | '.'       => some (10, 9)
  | _         => none

def prefixOp (op : Char) : Option Nat :=
  match op with
  | '+' | '-' => some 5
  | _         => none

def postfixOp (op : Char) : Option Nat :=
  match op with
  | '!' => some 7
  | _   => none

def mathLang : Language Char :=
  .mk perens prefixOp infixOp postfixOp

def tokenize (s : String) : Array (Token Char) :=
  let rec go (cs : List Char) : List (Token Char) :=
    match cs with
    | []    => []
    | '(' :: cs => (.paren '(') :: go cs
    | ')' :: cs => (.paren ')') :: go cs
    | c::cs => if c.isWhitespace
      then go cs
      else (if c.isAlphanum then .atom c else .op c) :: go cs
  .mk (go s.toList)

def parse (s : String) : ParseResult (Token Char) (SExp Char) :=
  let tokens := tokenize s
  let lexer := Lexer.mk (.mk (n := tokens.size) tokens (by omega))
  mathLang.mkParser.run lexer

#eval parse "- 1 * (2! + 3) - 4.5"
