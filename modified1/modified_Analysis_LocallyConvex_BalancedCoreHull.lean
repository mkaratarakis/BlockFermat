def balancedCore (s : Set E) :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t ⊆ s }
#align balanced_core balancedCore

def balancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s
#align balanced_core_aux balancedCoreAux

def balancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (_ : ‖r‖ ≤ 1), r • s
#align balanced_hull balancedHull