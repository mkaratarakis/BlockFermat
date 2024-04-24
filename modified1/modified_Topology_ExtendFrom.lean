def extendFrom (A : Set X) (f : X → Y) : X → Y :=
  fun x ↦ @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f
#align extend_from extendFrom