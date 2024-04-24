def homeomorphProd : TotalSpace F (Trivial B F) ≃ₜ B × F :=
  (TotalSpace.toProd _ _).toHomeomorphOfInducing (inducing_toProd B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : Trivialization F (π F (Bundle.Trivial B F)) where
  -- Porting note: golfed
  toPartialHomeomorph := (homeomorphProd B F).toPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl
#align bundle.trivial.trivialization Bundle.Trivial.trivialization

def Prod.toFun' : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → B × F₁ × F₂ :=
  fun p ↦ ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩
#align trivialization.prod.to_fun' Trivialization.Prod.toFun'

def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩
#align trivialization.prod.inv_fun' Trivialization.Prod.invFun'

def prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' x h := ⟨h, Set.mem_univ _⟩
  map_target' x h := h.1
  left_inv' x := Prod.left_inv
  right_inv' x := Prod.right_inv
  open_source := by
    convert (e₁.open_source.prod e₂.open_source).preimage
        (FiberBundle.Prod.inducing_diag F₁ E₁ F₂ E₂).continuous
    ext x
    simp only [Trivialization.source_eq, mfld_simps]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  continuousOn_toFun := Prod.continuous_to_fun
  continuousOn_invFun := Prod.continuous_inv_fun
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun x _ := rfl
#align trivialization.prod Trivialization.prod

def pullbackTopology : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓
    induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace F E)›
#align pullback_topology pullbackTopology

def Trivialization.pullback (e : Trivialization F (π F E)) (f : K) :
    Trivialization F (π F ((f : B' → B) *ᵖ E)) where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := @TotalSpace.mk _ F (f *ᵖ E) y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod, mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, Pullback.lift_proj] at h
    simp_rw [Pullback.lift, e.symm_apply_apply_mk h]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true_iff] at h
    simp_rw [Pullback.lift_mk, e.apply_mk_symm h]
  open_source := by
    simp_rw [e.source_eq, ← preimage_comp]
    exact e.open_baseSet.preimage ((map_continuous f).comp <| Pullback.continuous_proj F E f)
  open_target := ((map_continuous f).isOpen_preimage _ e.open_baseSet).prod isOpen_univ
  open_baseSet := (map_continuous f).isOpen_preimage _ e.open_baseSet
  continuousOn_toFun :=
    (Pullback.continuous_proj F E f).continuousOn.prod
      (continuous_snd.comp_continuousOn <|
        e.continuousOn.comp (Pullback.continuous_lift F E f).continuousOn Subset.rfl)
  continuousOn_invFun := by
    dsimp only
    simp_rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff, Function.comp,
      pullbackTotalSpaceEmbedding]
    refine'
      continuousOn_fst.prod
        (e.continuousOn_symm.comp ((map_continuous f).prod_map continuous_id).continuousOn
          Subset.rfl)
  source_eq := by
    dsimp only
    rw [e.source_eq]
    rfl
  target_eq := rfl
  proj_toFun y _ := rfl
#align trivialization.pullback Trivialization.pullback

structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `fun x ↦ E₁ x × E₂ x`).

* `FiberBundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags