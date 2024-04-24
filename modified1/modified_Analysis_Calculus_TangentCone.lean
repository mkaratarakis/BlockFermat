def tangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → 𝕜) (d : ℕ → E),
    (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto (fun n => ‖c n‖) atTop atTop ∧
    Tendsto (fun n => c n • d n) atTop (𝓝 y) }
#align tangent_cone_at tangentConeAt

def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt 𝕜 s x
#align unique_diff_on UniqueDiffOn

structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentCone : Dense (Submodule.span 𝕜 (tangentConeAt 𝕜 s x) : Set E)
  mem_closure : x ∈ closure s
#align unique_diff_within_at UniqueDiffWithinAt