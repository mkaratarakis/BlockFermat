def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in cobounded M, t ⊆ a • s
#align absorbs Absorbs

def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}
#align absorbent Absorbent