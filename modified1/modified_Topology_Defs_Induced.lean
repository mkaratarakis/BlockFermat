def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
#align topological_space.induced TopologicalSpace.induced

def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter s₁ s₂ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
#align topological_space.coinduced TopologicalSpace.coinduced

def QuotientMap {X : Type*} {Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) : Prop :=
  Function.Surjective f ∧ tY = tX.coinduced f
#align quotient_map QuotientMap

structure Inducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  induced : tX = tY.induced f
#align inducing Inducing

structure Embedding [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) extends
  Inducing f : Prop where
  /-- A topological embedding is injective. -/
  inj : Function.Injective f
#align embedding Embedding

structure OpenEmbedding (f : X → Y) extends Embedding f : Prop where
  /-- The range of an open embedding is an open set. -/
  isOpen_range : IsOpen <| range f
#align open_embedding OpenEmbedding

structure ClosedEmbedding (f : X → Y) extends Embedding f : Prop where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f
#align closed_embedding ClosedEmbedding