def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j
#align pairwise Pairwise

def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y
#align set.pairwise Set.Pairwise