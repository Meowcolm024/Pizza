import Pizza.Index
import Pizza.Parser

def perens (op : Char) : Option (Token Char → Bool) :=
  match op with
  | '(' => some (λ r => match r with | .op ')' => true | _ => false)
  | _   => none

def infixOp (op : Char) : Option (Nat × Nat) :=
  match op with
  | '+' | '-' => some (1, 2)
  | '*' | '/' => some (3, 4)
  | '.'       => some (10, 9)
  | _         => none

def mathLang : Language Char :=
  .mk perens (λ _ => .none) infixOp (λ _ => .none)

def tokenize (s : String) : Array (Token Char) :=
  let rec go (cs : List Char) : List (Token Char) :=
    match cs with
    | []    => []
    | c::cs => if c.isWhitespace
      then go cs
      else (if c.isAlphanum then .atom c else .op c) :: go cs
  .mk (go s.toList)

def parse (s : String) : ParseResult Char (SExp Char) :=
  let tokens := tokenize s
  let lexer := Lexer.mk (.mk (n := tokens.size) tokens (by omega))
  mathLang.mkParser.run lexer

#eval parse "1 * (2 + 3) - 4.5"
