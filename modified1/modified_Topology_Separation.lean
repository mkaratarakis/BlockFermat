def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V
#align separated_nhds SeparatedNhds

def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }
#align specialization_order specializationOrder

def Bornology.relativelyCompact : Bornology X where
  cobounded' := Filter.coclosedCompact X
  le_cofinite' := Filter.coclosedCompact_le_cofinite
#align bornology.relatively_compact Bornology.relativelyCompact

structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. Use `embedding_inclusion` instead. -/
@[deprecated embedding_inclusion]
theorem TopologicalSpace.subset_trans {s t : Set X} (ts : t ⊆ s) :
    (instTopologicalSpaceSubtype : TopologicalSpace t) =
      (instTopologicalSpaceSubtype : TopologicalSpace s).induced (Set.inclusion ts) :=
  (embedding_inclusion ts).induced
#align topological_space.subset_trans TopologicalSpace.subset_trans