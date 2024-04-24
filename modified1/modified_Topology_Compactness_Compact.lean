def inCompact : Bornology X where
  cobounded' := Filter.cocompact X
  le_cofinite' := Filter.cocompact_le_cofinite
#align bornology.in_compact Bornology.inCompact

def LocallyFinite.fintypeOfCompact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)
#align locally_finite.fintype_of_compact LocallyFinite.fintypeOfCompact