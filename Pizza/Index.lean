def IndexedArr (α β : Nat -> Type) (n : Nat) : Type := α n -> β n

infixr:60 "—→" => fun α β => IndexedArr α β

def IndexedType (α : Nat -> Type) : Type := ∀ {n} , α n

notation:50 "⟦" α:60 "⟧" => IndexedType α

structure Box (α : Nat -> Type) (n : Nat) where
  mk ::
  call : ∀ {m}, m < n -> α m

def map {α β} (f :  ⟦ α —→ β ⟧) : ⟦ Box α —→ Box β ⟧ :=
  λ b => .mk (λ ev => f (b.call ev))

def extract {α} (b :  ⟦ Box α ⟧) :  ⟦ α ⟧ :=
  b.call (Nat.le_refl _)

def ap {α β} (f :  ⟦ Box (α —→ β) ⟧) : ⟦ Box α —→ Box β ⟧ :=
  λ b => .mk (λ ev => f.call ev (b.call ev))

def fix {α} (f :  ⟦ Box α —→ α ⟧) :  ⟦ α ⟧ :=
  let rec go (f :  ⟦ Box α —→ α ⟧) :  ⟦ Box α ⟧ := λ {n} =>
    match n with
    | 0     => .mk (λ _ => by contradiction)
    | n + 1 => .mk (λ _ => f (go f))
  extract (go f)
