import Pizza.Index

inductive Token (τ : Type) where
| atom : τ → Token τ
| op   : τ → Token τ

deriving instance Repr, Inhabited, DecidableEq for Token

instance [ToString τ] : ToString (Token τ) where
  toString
  | .atom a => s!"{a}"
  | .op op  => s!"{op}"

structure Lexer (τ : Type) (n : Nat) where
  mk     ::
  tokens : Vector (Token τ) n

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
  rem : List (Token τ)

deriving instance Repr, Inhabited for ParseError

@[reducible]
def ParseResult (τ : Type) : Type → Type := Except (ParseError τ)

structure Parser (τ α : Type) (n : Nat) where
  mk       ::
  parseAux : ∀ {m}, m ≤ n → Lexer τ m → (lhs : α) → (mbp : Nat) → ParseResult τ (Option (Success τ α m))
  parse    : ∀ {m}, m ≤ n → Lexer τ m → (mbp : Nat) → ParseResult τ (Success τ α m)

inductive SExp (τ : Type) : Type where
| atom : τ → SExp τ
| cons : τ → List (SExp τ) → SExp τ

deriving instance Repr, Inhabited for SExp

instance {τ} [ToString τ] : ToString (SExp τ) where
  toString :=
    let rec go (s : SExp τ) := match s with
      | .atom a    => s!"{a}"
      | .cons f s' =>
        let r := s'.foldl (λ x y => x ++ " " ++ go y) ""
        s!"({f}{r})"
    go

structure Language (τ : Type) where
  mk        ::
  parens    : τ → Option (Token τ → Bool)
  prefixOp  : τ → Option Nat
  infixeOp  : τ → Option (Nat × Nat)
  postfixOp : τ → Option Nat

def asParseResult {α τ} (opt : Option α) (msg : String) (rem : List (Token τ)) : ParseResult τ α :=
  match opt with
  | .some x => .ok x
  | .none   => .error (.mk msg rem)

def Lexer.nextTokenOpt {n τ} (lexer : Lexer τ n) : Option (Success τ (Token τ) n) :=
  match n, lexer.tokens with
  | 0    , _  => .none
  | n + 1, ts => return .mk ts.head (by omega) (.mk ts.tail)

def Lexer.nextToken {n τ} (lexer : Lexer τ n) : ParseResult τ (Success τ (Token τ) n) :=
  match lexer.nextTokenOpt with
  | .some t => .ok t
  | .none   => .error (.mk "unexpected eof" lexer.tokens.toList)

def Parser.run {n τ α} (lexer : Lexer τ n) (parser : Parser τ α n) : ParseResult τ α :=
  (parser.parse (by omega) lexer 0).map (λ r => r.value)

def Language.mkParser {τ} [ToString τ] (lang : Language τ) : ⟦ Parser τ (SExp τ) ⟧ :=
  fix (λ rec => .mk
  (λ ev lexer lhs mbp => do
    if let .some (Success.mk value small lexer) := lexer.nextTokenOpt then
      let p := rec.call (Nat.le_trans small ev)
      match value with
      | .op op =>
        if let .some (lbp, rbp) := lang.infixeOp op then
          if lbp < mbp then .ok .none
          else
            let (Success.mk rhs small lexer) <- p.parse (by omega) lexer rbp
            let res := SExp.cons op [lhs, rhs]
            let auxres <- p.parseAux (by omega) lexer res mbp
            return return match auxres with
            | .some (Success.mk r s t) => .mk r (by omega) t
            | .none => .mk res (by omega) lexer
        else
          .ok .none
      | _ => .error (.mk s!"failed to parse {value}" lexer.tokens.toList)
    else
      .ok .none
  )
  (λ ev lexer mbp => do
    let (Success.mk value small lexer) <- lexer.nextToken
    let p := rec.call (Nat.le_trans small ev)
    match value with
    | .atom a =>
      let auxres <- p.parseAux (by omega) lexer (.atom a) mbp
      match auxres with
      | .some (Success.mk r s t) => .ok (.mk r (by omega) t)
      | .none => .ok (.mk (.atom a) small lexer)
    | .op op =>
      let matched <- asParseResult (lang.parens op) s!"failed to parse parens {op}" lexer.tokens.toList
      let (Success.mk lhs small lexer) <- p.parse (by omega) lexer 0
      let (Success.mk pr small lexer) <- lexer.nextToken
      if matched pr then
        let auxres <- p.parseAux (by omega) lexer lhs mbp
        return match auxres with
        | .some (Success.mk r s t) => .mk r (by omega) t
        | .none => .mk lhs (by omega) lexer
      else
        .error (.mk s!"paren {op} is not closed by {pr}" lexer.tokens.toList)
  ))
