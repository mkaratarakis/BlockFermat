def Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded' := comap f (cobounded β)
  le_cofinite' := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)
#align bornology.induced Bornology.induced

structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {π : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (π i)]

instance Prod.instBornology : Bornology (α × β) where
  cobounded' := (cobounded α).coprod (cobounded β)
  le_cofinite' :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite
#align prod.bornology Prod.instBornology