def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x
#align is_chain IsChain

def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t
#align super_chain SuperChain

def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t
#align is_max_chain IsMaxChain

def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then h.choose else s
#align succ_chain SuccChain

def maxChain (r : α → α → Prop) : Set α :=
  ⋃₀ setOf (ChainClosure r)
#align max_chain maxChain

structure Flag (α : Type*) [LE α] where
  /-- The `carrier` of a flag is the underlying set. -/
  carrier : Set α
  /-- By definition, a flag is a chain -/
  Chain' : IsChain (· ≤ ·) carrier
  /-- By definition, a flag is a maximal chain -/
  max_chain' : ∀ ⦃s⦄, IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s
#align flag Flag