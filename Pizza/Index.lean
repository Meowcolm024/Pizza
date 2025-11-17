@[reducible]
def IndexedType (α : Nat -> Type) : Type := ∀ {n} , α n

notation:50 "⟦" α:60 "⟧" => IndexedType α

@[reducible]
def IndexedArr (α β : Nat -> Type) (n : Nat) : Type := α n -> β n

infixr:60 "—→" => fun α β => IndexedArr α β

structure Box (α : Nat -> Type) (n : Nat) where
  mk   ::
  call : ∀ {m}, m < n -> α m

prefix:70 "□" => fun α => Box α

def map {α β} (f : ⟦ α —→ β ⟧) : ⟦ □ α —→ □ β ⟧ :=
  λ b => .mk (λ ev => f (b.call ev))

def extract {α} (b : ⟦ □ α ⟧) : ⟦ α ⟧ :=
  b.call (by apply Nat.le_refl)

def ap {α β} (f : ⟦ □ (α —→ β) ⟧) : ⟦ □ α —→ □ β ⟧ :=
  λ b => .mk (λ ev => f.call ev (b.call ev))

def fix {α} (f : ⟦ □ α —→ α ⟧) : ⟦ α ⟧ :=
  let rec go (f : ⟦ □ α —→ α ⟧) : ⟦ □ α ⟧ :=
    λ {n} => match n with
      | 0     => .mk (λ _ => by contradiction)
      | n + 1 => .mk (λ _ => f (go f))
  extract (go f)
