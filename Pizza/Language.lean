import Pizza.Index
import Pizza.Parser

namespace Language

inductive Token (τ : Type) where
| atom : τ → Token τ
| op   : τ → Token τ

deriving instance Repr, Inhabited, DecidableEq for Token

instance {τ} [ToString τ] : ToString (Token τ) where
  toString
  | .atom a  => s!"{a}"
  | .op op   => s!"{op}"

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
  parens    : τ → Option (τ → Bool)
  prefixOp  : τ → Option Nat
  infixeOp  : τ → Option (Nat × Nat)
  postfixOp : τ → Option Nat

private def asParseResult {α τ} (opt : Option α) (msg : String) (rem : List τ) : ParseResult τ α :=
  match opt with
  | .some x => .ok x
  | .none   => .error (.mk msg rem)

private def matchParen (f : τ → Bool) (t : Token τ) : Bool :=
  match t with
  | .op p => f p
  | _     => false

notation auxres "aux" alt =>
  match auxres with
  | some (Success.mk r s t) => Success.mk r (by omega) t
  | none => alt

def Language.mkParser {τ} [ToString τ] (lang : Language τ) : ⟦ Parser (Token τ) (SExp τ) ⟧ :=
  fix (λ rec => .mk
  (λ ev lexer lhs mbp => do
    if let some (Success.mk value small lexer) := lexer.nextTokenOpt then
      let p := rec.call (Nat.le_trans small ev)
      match value with
      | .op op =>
        if let some lbp := lang.postfixOp op then
          if lbp >= mbp then
            let res := (.cons op [lhs])
            let auxres <- p.parseAux (by omega) lexer res mbp
            return return auxres aux .mk res (by omega) lexer
        if let some (lbp, rbp) := lang.infixeOp op then
          if lbp < mbp then return none
          else
            let (Success.mk rhs small lexer) <- p.parse (by omega) lexer rbp
            let res := SExp.cons op [lhs, rhs]
            let auxres <- p.parseAux (by omega) lexer res mbp
            return return auxres aux .mk res (by omega) lexer
        -- note that we do not consume the operator token when there is no match
        -- so the parser terminates here, leaving the remaining tokens not consumed
        return none
      | _ => .error (.mk s!"failed to parse {value}" lexer.tokens.toList)
    return none
  )
  (λ ev lexer mbp => do
    let (Success.mk value small lexer) <- lexer.nextToken
    let p := rec.call (Nat.le_trans small ev)
    match value with
    | .atom a =>
      let auxres <- p.parseAux (by omega) lexer (.atom a) mbp
      return auxres aux Success.mk (.atom a) (by omega) lexer
    | .op op =>
      if let .some matched := lang.parens op then
        let (Success.mk lhs small lexer) <- p.parse (by omega) lexer 0
        let (Success.mk rpr small lexer) <- lexer.nextToken
        if matchParen matched rpr then
          let auxres <- p.parseAux (by omega) lexer lhs mbp
          return auxres aux .mk lhs (by omega) lexer
      if let .some rbp := lang.prefixOp op then
        let (Success.mk lhs small lexer) <- p.parse (by omega) lexer rbp
        let res := .cons op [lhs]
        let auxres <- p.parseAux (by omega) lexer res mbp
        return auxres aux .mk res (by omega) lexer
      .error (.mk s!"failed to parse {op}" lexer.tokens.toList)
  ))
