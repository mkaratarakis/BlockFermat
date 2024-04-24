def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s
#align filter.lift Filter.lift

def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)
#align filter.lift' Filter.lift'

def {f : Filter α} {g : Filter β} :
    f ×ˢ g = f.lift fun s => g.lift' fun t => s ×ˢ t := by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using iInf_congr fun i => iInf_comm
#align filter.prod_def Filter.prod_def