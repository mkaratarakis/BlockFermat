def Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2
#align isometry Isometry

def mk' {α : Type u} [EMetricSpace α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
    (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
  left_inv _ := hf.injective <| hfg _
  right_inv := hfg
  isometry_toFun := hf
#align isometry_equiv.mk' IsometryEquiv.mk'

def refl (α : Type*) [PseudoEMetricSpace α] : α ≃ᵢ α :=
  { Equiv.refl α with isometry_toFun := isometry_id }
#align isometry_equiv.refl IsometryEquiv.refl

def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }
#align isometry_equiv.trans IsometryEquiv.trans

def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
  isometry_toFun := h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm
#align isometry_equiv.symm IsometryEquiv.symm

def Simps.apply (h : α ≃ᵢ β) : α → β := h
#align isometry_equiv.simps.apply IsometryEquiv.Simps.apply

def Simps.symm_apply (h : α ≃ᵢ β) : β → α :=
  h.symm
#align isometry_equiv.simps.symm_apply IsometryEquiv.Simps.symm_apply

def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β where
  continuous_toFun := h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv
#align isometry_equiv.to_homeomorph IsometryEquiv.toHomeomorph

def funUnique [Unique ι] [Fintype ι] : (ι → α) ≃ᵢ α where
  toEquiv := Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]
#align isometry_equiv.fun_unique IsometryEquiv.funUnique

def piFinTwo (α : Fin 2 → Type*) [∀ i, PseudoEMetricSpace (α i)] : (∀ i, α i) ≃ᵢ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]
#align isometry_equiv.pi_fin_two IsometryEquiv.piFinTwo

def Isometry.isometryEquivOnRange [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : Isometry f) : α ≃ᵢ range f where
  isometry_toFun := h
  toEquiv := Equiv.ofInjective f h.injective
#align isometry.isometry_equiv_on_range Isometry.isometryEquivOnRange

structure on the source space. -/
theorem UniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α → β}
    (h : UniformEmbedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl
#align uniform_embedding.to_isometry UniformEmbedding.to_isometry

structure on the source space. -/
theorem Embedding.to_isometry {α β} [TopologicalSpace α] [MetricSpace β] {f : α → β}
    (h : Embedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl
#align embedding.to_isometry Embedding.to_isometry

structure IsometryEquiv (α : Type u) (β : Type v) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    extends α ≃ β where
  isometry_toFun : Isometry toFun
#align isometry_equiv IsometryEquiv