def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s
#align convex Convex

def convexAddSubmonoid : AddSubmonoid (Set E) where
  carrier := {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add
#align convex_add_submonoid convexAddSubmonoid

def stdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }
#align std_simplex stdSimplex