def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise rᶜ
#align is_antichain IsAntichain

def IsStrongAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise fun a b => ∀ c, ¬r a c ∨ ¬r b c
#align is_strong_antichain IsStrongAntichain

def IsWeakAntichain (s : Set (∀ i, α i)) : Prop :=
  IsAntichain (· ≺ ·) s
#align is_weak_antichain IsWeakAntichain