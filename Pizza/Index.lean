namespace Index

def IK (α : Type) (_ : Nat) : Type := α

def IArr (α β : Nat -> Type) (n : Nat) : Type := α n -> β n

def IProd (α β : Nat -> Type) (n : Nat) : Type := α n × β n

def IType (α : Nat -> Type) : Type := ∀ {n} , α n

structure Box (α : Nat -> Type) (n : Nat) where
  mk ::
  call : ∀ {m}, m < n -> α m

def map (f : IType (IArr α β)) : IType (IArr (Box α) (Box β)) :=
  λ b => .mk (λ ev => f (b.call ev))

def extract (b : IType (Box α)) : IType α :=
  b.call (Nat.le_refl _)

def ap (f : IType (Box (IArr α β))) : IType (IArr (Box α) (Box β)) :=
  λ b => .mk (λ ev => f.call ev (b.call ev))

def fix (f : IType (IArr (Box α) α)) : IType α :=
  let rec fix1 (f : IType (IArr (Box α) α)) : IType (Box α) := λ {n} =>
    match n with
    | 0 => .mk (λ ev => by contradiction)
    | n + 1 => .mk (λ ev => f (fix1 f))
  extract (fix1 f)

inductive Token : Type where
| atom : Char → Token
| op   : Char → Token
| eof  : Token

def tokenize (s : String) : Array Token :=
  let rec go (cs : List Char) : List Token :=
    match cs with
    | []    => []
    | c::cs => if c.isWhitespace
      then go cs
      else (if c.isAlphanum then .atom c else .op c) :: go cs
  .mk (go s.toList)

deriving instance Repr, Inhabited, DecidableEq for Token

structure Lexer (n : Nat) where
  mk ::
  tokens : Vector Token n

inductive SExp : Type where
| atom : Char → SExp
| cons : Char → List SExp → SExp

instance ShowSExp : ToString SExp where
  toString :=
    let rec go (s : SExp) := match s with
      | .atom a    => s!"{a}"
      | .cons f s' =>
        let r := s'.foldl (λ x y => x ++ " " ++ go y) ""
        s!"({f}{r})"
    go

deriving instance Repr, Inhabited for SExp

structure Success (α : Type) (n : Nat) where
  mk ::
  value : α
  {size : Nat}
  small : size < n
  rest  : Lexer size

def Lexer.nextToken (lex : Lexer n) : Option (Success Token n) :=
  match n, lex.tokens with
  | 0, _ => .none
  | n + 1, ts => return .mk ts.head (by omega) (.mk ts.tail)

def infixOp (op : Char) : Option (Nat × Nat) :=
  match op with
  | '+' | '-' => return (1, 2)
  | '*' | '/' => return (3, 4)
  | '.'       => return (10, 9)
  | _         => .none

structure Parser (α : Type) (n : Nat) where
  mk ::
  parseAux : ∀ {m}, m ≤ n → Lexer m → (lhs : α) → (mbp : Nat) → Option (Success α m ⊕ Unit)
  parse    : ∀ {m}, m ≤ n → Lexer m → (mbp : Nat) → Option (Success α m)

def parser : IType (Parser SExp) :=
  fix (λ rec => .mk
  (λ ev lex lhs mbp => do
    if let .some (Success.mk value small lex') := lex.nextToken then
      let p := rec.call (Nat.le_trans small ev)
      match value with
      | .op op =>
        let (lbp, rbp) <- infixOp op
        if lbp < mbp then
          return .inr ()
        else
          let (Success.mk rhs small' lex'') <- p.parse (by omega) lex' rbp
          let p' := rec.call (Nat.le_trans small' (Nat.le_trans (Nat.le_of_lt small) ev))
          let res := SExp.cons op [lhs, rhs]
          let auxres <- p.parseAux (by omega) lex'' res mbp
          match auxres with
          | .inl (Success.mk r s t) =>
            return .inl (.mk r (by omega) lex'')
          | .inr () =>
            return .inl (.mk res (by omega) lex'')
      | _ => .none
    else
      return .inr ()
  )
  (λ ev lex mbp => do
    let (Success.mk value small lex') <- lex.nextToken
    let p := rec.call (Nat.le_trans small ev)
    match value with
    | .atom a =>
      let auxres <- p.parseAux (by omega) lex' (.atom a) mbp
      match auxres with
      | .inl (Success.mk r s t) =>
        return .mk r (Nat.le_of_lt (Nat.le_trans (by omega) small)) t
      | .inr () =>
        return .mk (.atom a) small lex'
    | _ => .none
  ))

def Parser.run (lex : Lexer n) (parser : Parser SExp n) : Option SExp :=
  (parser.parse (by omega) lex 0).map (λ r => r.value)

def parse (s : String) : Option SExp :=
  let sa := tokenize s
  let lex := Lexer.mk (n := sa.size) (Vector.mk sa (by omega))
  parser.run lex

#eval parse "1 + 2 * 3 + 4"
