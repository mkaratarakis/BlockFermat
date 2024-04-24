def WCovBy (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b
#align wcovby WCovBy

def CovBy (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b
#align covby CovBy