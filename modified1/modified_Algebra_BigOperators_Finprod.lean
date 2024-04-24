def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : (support (f ∘ PLift.down)).Finite then ∑ i in h.toFinset, f i.down else 0
#align finsum finsum

def finprod (lemma := finprod_def') (f : α → M) : M :=
  if h : (mulSupport (f ∘ PLift.down)).Finite then ∏ i in h.toFinset, f i.down else 1
#align finprod finprod

def (s : Set α) (f : α → M) : ∏ᶠ a ∈ s, f a = ∏ᶠ a, mulIndicator s f a :=
  finprod_congr <| finprod_eq_mulIndicator_apply s f
#align finprod_mem_def finprod_mem_def

def finsum_mem_def

@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) :
    ∏ᶠ i, f i = ∏ i in s, f i := by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage _).symm
  have : mulSupport (f ∘ PLift.down) ⊆ s.map Equiv.plift.symm.toEmbedding := by
    rw [A, Finset.coe_map]
    exact image_subset _ h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  congr
#align finprod_eq_prod_of_mul_support_subset finprod_eq_prod_of_mulSupport_subset

def (f : α → M) [Decidable (mulSupport f).Finite] :
    ∏ᶠ i : α, f i = if h : (mulSupport f).Finite then ∏ i in h.toFinset, f i else 1 := by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h
#align finprod_def finprod_def

def finsum_def

@[to_additive]
theorem finprod_of_infinite_mulSupport {f : α → M} (hf : (mulSupport f).Infinite) :
    ∏ᶠ i, f i = 1 := by classical rw [finprod_def, dif_neg hf]
#align finprod_of_infinite_mul_support finprod_of_infinite_mulSupport