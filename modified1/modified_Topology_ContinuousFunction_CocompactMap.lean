def toCocompactMap (f : F) : CocompactMap α β :=
  { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }

instance : CoeTC F (CocompactMap α β) :=
  ⟨toCocompactMap⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance : FunLike (CocompactMap α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : CocompactMapClass (CocompactMap α β) α β where
  map_continuous f := f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

@[simp]
theorem coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α → β) = f :=
  rfl
#align cocompact_map.coe_to_continuous_fun CocompactMap.coe_toContinuousMap

def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'
#align cocompact_map.copy CocompactMap.copy

def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩
#align cocompact_map.id CocompactMap.id

def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩
#align cocompact_map.comp CocompactMap.comp

def Homeomorph.toCocompactMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) : CocompactMap α β where
  toFun := f
  continuous_toFun := f.continuous
  cocompact_tendsto' := by
    refine' CocompactMap.tendsto_of_forall_preimage fun K hK => _
    erw [K.preimage_equiv_eq_image_symm]
    exact hK.image f.symm.continuous
#align homeomorph.to_cocompact_map Homeomorph.toCocompactMap

structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β : Type max u v where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)
#align cocompact_map CocompactMap