def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)
#align finset.sup_indep Finset.SupIndep

def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sSup (s \ {a}))
#align complete_lattice.set_independent CompleteLattice.SetIndependent

def Independent {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)
#align complete_lattice.independent CompleteLattice.Independent

def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl
#align complete_lattice.independent_def CompleteLattice.independent_def