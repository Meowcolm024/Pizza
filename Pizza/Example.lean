import Pizza.Language
import Pizza.Parser

namespace Example

open Language

def perens (op : Char) : Option (Char → Bool) :=
  match op with
  | '(' => some (λ r => r == ')')
  | _   => none

def infixOp (op : Char) : Option (Nat × Nat × Option (Char → Bool)) :=
  match op with
  | '='       => some (3, 2, none)
  | '?'       => some (5, 4, some λ c => c == ':')
  | '+' | '-' => some (6, 7, none)
  | '*' | '/' => some (8, 9, none)
  | '.'       => some (15, 14, none)
  | _         => none

def prefixOp (op : Char) : Option (Nat × Option (Char → Bool)) :=
  match op with
  | 'λ'       => some (2, some λ c => c == '→')
  | '+' | '-' => some (10, none)
  | _         => none

def postfixOp (op : Char) : Option (Nat × Option (Char → Bool)) :=
  match op with
  | '!' => some (12 , none)
  | '[' => some (12 , some λ c => c == ']')
  | _   => none

def exampleLang : Language Char :=
  .mk perens prefixOp infixOp postfixOp

def tokenize (s : String) : Array (Token Char) :=
  let rec go (cs : List Char) : List (Token Char) :=
    match cs with
    | []    => []
    | c::cs => if c.isWhitespace
      then go cs
      else (if c.isAlphanum then .atom c else .op c) :: go cs
  .mk (go s.toList)

def parse (s : String) : ParseResult (Token Char) (SExp Char × List (Token Char)) :=
  let tokens := tokenize s
  let lexer := Lexer.mk (.mk (n := tokens.size) tokens (by omega))
  (exampleLang.mkParser.run lexer).map (λ r => (r.value, r.rest.tokens.toList))

#eval parse "- 1 * (2! + 3) - 4.5"
#eval parse "((1))"
#eval parse "(λ 2 = 3 → 1 + (2 ? 3[4.5] : 6!)) * (4 + 5)"
