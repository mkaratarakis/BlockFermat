def polar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, ‖B x y‖ ≤ 1 }
#align linear_map.polar LinearMap.polar