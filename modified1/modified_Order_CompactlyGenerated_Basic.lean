def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), SupClosed s → sSup s ∈ s
#align complete_lattice.is_sup_closed_compact CompleteLattice.IsSupClosedCompact

def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id
#align complete_lattice.is_Sup_finite_compact CompleteLattice.IsSupFiniteCompact

def IsCompactElement {α : Type*} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id
#align complete_lattice.is_compact_element CompleteLattice.IsCompactElement