def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then f x else 1
#align set.mul_indicator Set.mulIndicator

def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α → M) →* α → M
    where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s
#align set.mul_indicator_hom Set.mulIndicatorHom