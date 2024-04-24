def denseSeq [SeparableSpace α] [Nonempty α] : ℕ → α :=
  Classical.choose (exists_dense_seq α)
#align topological_space.dense_seq TopologicalSpace.denseSeq

def IsSeparable (s : Set α) :=
  ∃ c : Set α, c.Countable ∧ s ⊆ closure c
#align topological_space.is_separable TopologicalSpace.IsSeparable

def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).choose
#align topological_space.countable_basis TopologicalSpace.countableBasis

structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards.  -/
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  /-- The sets from `s` cover the whole space. -/
  sUnion_eq : ⋃₀ s = univ
  /-- The topology is generated by sets from `s`. -/
  eq_generateFrom : t = generateFrom s
#align topological_space.is_topological_basis TopologicalSpace.IsTopologicalBasis