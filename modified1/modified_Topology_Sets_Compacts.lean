def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe)

protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.compacts.is_compact TopologicalSpace.Compacts.isCompact

def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩
#align topological_space.compacts.map TopologicalSpace.Compacts.map

def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.continuous
  invFun := Compacts.map _ f.symm.continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]
#align topological_space.compacts.equiv TopologicalSpace.Compacts.equiv

def prod (K : Compacts α) (L : Compacts β) : Compacts (α × β) where
  carrier := K ×ˢ L
  isCompact' := IsCompact.prod K.2 L.2
#align topological_space.compacts.prod TopologicalSpace.Compacts.prod

def Simps.coe (s : NonemptyCompacts α) : Set α := s

initialize_simps_projections NonemptyCompacts (carrier → coe)

protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.nonempty_compacts.is_compact TopologicalSpace.NonemptyCompacts.isCompact

def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.isCompact.isClosed⟩
#align topological_space.nonempty_compacts.to_closeds TopologicalSpace.NonemptyCompacts.toCloseds

def prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : NonemptyCompacts (α × β) :=
  { K.toCompacts.prod L.toCompacts with nonempty' := K.nonempty.prod L.nonempty }
#align topological_space.nonempty_compacts.prod TopologicalSpace.NonemptyCompacts.prod

def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier → coe)

protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.positive_compacts.is_compact TopologicalSpace.PositiveCompacts.isCompact

def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.nonempty⟩
#align topological_space.positive_compacts.to_nonempty_compacts TopologicalSpace.PositiveCompacts.toNonemptyCompacts

def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (K : PositiveCompacts α) :
    PositiveCompacts β :=
  { Compacts.map f hf K.toCompacts with
    interior_nonempty' :=
      (K.interior_nonempty'.image _).mono (hf'.image_interior_subset K.toCompacts) }
#align topological_space.positive_compacts.map TopologicalSpace.PositiveCompacts.map

def prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    PositiveCompacts (α × β) where
  toCompacts := K.toCompacts.prod L.toCompacts
  interior_nonempty' := by
    simp only [Compacts.carrier_eq_coe, Compacts.coe_prod, interior_prod_eq]
    exact K.interior_nonempty.prod L.interior_nonempty
#align topological_space.positive_compacts.prod TopologicalSpace.PositiveCompacts.prod

def Simps.coe (s : CompactOpens α) : Set α := s

initialize_simps_projections CompactOpens (carrier → coe)

protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.isCompact'
#align topological_space.compact_opens.is_compact TopologicalSpace.CompactOpens.isCompact

def toOpens (s : CompactOpens α) : Opens α := ⟨s, s.isOpen⟩
#align topological_space.compact_opens.to_opens TopologicalSpace.CompactOpens.toOpens

def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.isCompact.isClosed, s.isOpen⟩
#align topological_space.compact_opens.to_clopens TopologicalSpace.CompactOpens.toClopens

def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.isOpen⟩
#align topological_space.compact_opens.map TopologicalSpace.CompactOpens.map

def prod (K : CompactOpens α) (L : CompactOpens β) : CompactOpens (α × β) :=
  { K.toCompacts.prod L.toCompacts with isOpen' := K.isOpen.prod L.isOpen }
#align topological_space.compact_opens.prod TopologicalSpace.CompactOpens.prod

structure Compacts (α : Type*) [TopologicalSpace α] where
  carrier : Set α
  isCompact' : IsCompact carrier
#align topological_space.compacts TopologicalSpace.Compacts

structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty
#align topological_space.nonempty_compacts TopologicalSpace.NonemptyCompacts

structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty
#align topological_space.positive_compacts TopologicalSpace.PositiveCompacts

structure CompactOpens (α : Type*) [TopologicalSpace α] extends Compacts α where
  isOpen' : IsOpen carrier
#align topological_space.compact_opens TopologicalSpace.CompactOpens