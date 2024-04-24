def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier → coe, as_prefix coe)

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.closeds.ext TopologicalSpace.Closeds.ext

def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩
#align topological_space.closeds.closure TopologicalSpace.Closeds.closure

def gi : GaloisInsertion (@Closeds.closure α _) (↑) where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq _s hs := SetLike.coe_injective <| subset_closure.antisymm hs
#align topological_space.closeds.gi TopologicalSpace.Closeds.gi

def {ι} (s : ι → Closeds α) :
    ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩ := by ext1; simp
#align topological_space.closeds.infi_def TopologicalSpace.Closeds.iInf_def

def _
#align topological_space.closeds.infi_mk TopologicalSpace.Closeds.iInf_mk

def singleton [T1Space α] (x : α) : Closeds α :=
  ⟨{x}, isClosed_singleton⟩
#align topological_space.closeds.singleton TopologicalSpace.Closeds.singleton

def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩
#align topological_space.closeds.compl TopologicalSpace.Closeds.compl

def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩
#align topological_space.opens.compl TopologicalSpace.Opens.compl

def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl
#align topological_space.closeds.compl_order_iso TopologicalSpace.Closeds.complOrderIso

def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl
#align topological_space.opens.compl_order_iso TopologicalSpace.Opens.complOrderIso

def Simps.coe (s : Clopens α) : Set α := s

initialize_simps_projections Clopens (carrier → coe)

/-- Reinterpret a clopen as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.isClopen.isOpen⟩
#align topological_space.clopens.to_opens TopologicalSpace.Clopens.toOpens

structure Closeds (α : Type*) [TopologicalSpace α] where
  carrier : Set α
  closed' : IsClosed carrier
#align topological_space.closeds TopologicalSpace.Closeds

structure Clopens (α : Type*) [TopologicalSpace α] where
  carrier : Set α
  isClopen' : IsClopen carrier
#align topological_space.clopens TopologicalSpace.Clopens