def maximals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → r b a }
#align maximals maximals

def minimals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → r a b }
#align minimals minimals