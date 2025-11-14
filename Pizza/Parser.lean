import Pizza.Index

structure Lexer (τ : Type) (n : Nat) where
  mk     ::
  tokens : Vector τ n

deriving instance Repr, Inhabited for Lexer

structure Success (τ α : Type) (n : Nat) where
  mk    ::
  value : α
  {size : Nat}
  small : size < n
  rest  : Lexer τ size

structure ParseError (τ : Type) where
  mk  ::
  msg : String
  rem : List τ

deriving instance Repr, Inhabited for ParseError

@[reducible]
def ParseResult (τ : Type) : Type → Type := Except (ParseError τ)

structure Parser (τ α : Type) (n : Nat) where
  mk       ::
  parseAux : ∀ {m}, m ≤ n → Lexer τ m → (lhs : α) → (mbp : Nat) → ParseResult τ (Option (Success τ α m))
  parse    : ∀ {m}, m ≤ n → Lexer τ m → (mbp : Nat) → ParseResult τ (Success τ α m)

def Lexer.nextTokenOpt {n τ} (lexer : Lexer τ n) : Option (Success τ τ n) :=
  match n, lexer.tokens with
  | 0    , _  => .none
  | n + 1, ts => return .mk ts.head (by omega) (.mk ts.tail)

def Lexer.nextToken {n τ} (lexer : Lexer τ n) : ParseResult τ (Success τ τ n) :=
  match lexer.nextTokenOpt with
  | .some t => .ok t
  | .none   => .error (.mk "unexpected eof" lexer.tokens.toList)

def Parser.run {n τ α} (lexer : Lexer τ n) (parser : Parser τ α n) : ParseResult τ α :=
  (parser.parse (by omega) lexer 0).map (λ r => r.value)
