def cofinite : Filter α :=
  comk Set.Finite finite_empty (fun _t ht _s hsub ↦ ht.subset hsub) fun _ h _ ↦ h.union
#align filter.cofinite Filter.cofinite