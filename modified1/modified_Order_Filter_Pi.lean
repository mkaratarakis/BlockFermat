def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)
#align filter.pi Filter.pi

def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
#align filter.Coprod Filter.coprodᵢ