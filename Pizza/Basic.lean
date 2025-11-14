import Pizza.Index

inductive Token : Type where
| atom : Char → Token
| op   : Char → Token
| eof  : Token

deriving instance Repr, Inhabited, DecidableEq for Token

structure Lexer where
  mk ::
  tokens : List Token

deriving instance Repr, Inhabited for Lexer

def Lexer.new (s : String) : Lexer :=
  let rec go (cs : List Char) : List Token :=
    match cs with
    | []    => []
    | c::cs => if c.isWhitespace
      then go cs
      else (if c.isAlphanum then .atom c else .op c) :: go cs
  .mk (go s.toList)

def Lexer.next (self : Lexer) : Token × Lexer :=
  match self.tokens with
  | []    => (.eof , self)
  | t::ts => (t , .mk ts)

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

def peekToken {m} [Monad m] [MonadState Lexer m] [MonadExcept String m] : m Token := do
  let lexer <- MonadState.get
  return lexer.next.fst

def nextToken {m} [Monad m] [MonadState Lexer m] [MonadExcept String m] : m Token := do
  let lexer <- MonadState.get
  let (t, lexer') := lexer.next
  MonadState.set lexer'
  return t

#eval Lexer.new "1 + 1"

def infixOp {m} [Monad m] [MonadExcept String m] (op : Char) : m (Nat × Nat) :=
  match op with
  | '+' | '-' => return (1, 2)
  | '*' | '/' => return (3, 4)
  | '.'       => return (10, 9)
  | _         => throw s!"unknown operator {op}"

def infixOp' (op : Char) : Except String (Nat × Nat) := Id.run (ExceptT.run (infixOp op))

def prefixOp {m} [Monad m] [MonadExcept String m] (op : Char) : m Nat :=
  match op with
  | '+' | '-' => return 5
  | _         => throw s!"unknown operator {op}"

def prefixOp' (op : Char) : Except String Nat := Id.run (ExceptT.run (prefixOp op))

def postfixOp {m} [Monad m] [MonadExcept String m] (op : Char)  : m Nat :=
  match op with
  | '!' => return 7
  | _   => throw s!"unknown operator {op}"

def postfixOp' (op : Char) : Except String Nat := Id.run (ExceptT.run (postfixOp op))

mutual

partial def parseAux {m} [Monad m] [MonadState Lexer m] [MonadExcept String m]
  (lhs : SExp) (mbp : Nat) : m SExp := do
  let t <- peekToken
  match t with
  | .op op =>
    if let .ok lbp := postfixOp' op then
      if lbp >= mbp then do
        _ <- nextToken
        let res <- parseAux (.cons op [lhs]) mbp
        return res
    if let .ok (lbp, rbp) := infixOp' op then do
      if lbp < mbp then return lhs
      _ <- nextToken
      let rhs <- parse rbp
      let res <- parseAux (.cons op [lhs, rhs]) mbp
      return res
    return lhs
  | .eof => return lhs
  | _ => throw "failed to parse"

partial def parse {m} [Monad m] [MonadState Lexer m] [MonadExcept String m]
  (mbp : Nat) : m SExp := do
  let t <- nextToken
  let lhs <- match t with
    | .atom a => pure (.atom a)
    | .op '(' => do
      let lhs <- parse 0
      _ <- nextToken
      pure lhs
    | .op op => do
      let rbp <- prefixOp op
      let rhs <- parse rbp
      pure (.cons op [rhs])
    | _ => throw "failed to parse"
  parseAux lhs mbp

end

partial def runParser (s : String) : String :=
    match StateT.run' (ExceptT.run (parse (m := ExceptT String (StateM Lexer)) 0)) (Lexer.new s) with
    | .ok r    => ShowSExp.toString r
    | .error m => m

#eval runParser "1 + 2 * 3.4"
#eval runParser "- 1 + 2"
#eval runParser "- 0.1 * (2 - 3) + 4 !"
