def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩
#align continuous_map.equiv_bounded_of_compact ContinuousMap.equivBoundedOfCompact

def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddHom α β, (equivBoundedOfCompact α β).symm with } : (α →ᵇ β) ≃+ C(α, β)).symm
#align continuous_map.add_equiv_bounded_of_compact ContinuousMap.addEquivBoundedOfCompact

def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β
#align continuous_map.isometry_equiv_bounded_of_compact ContinuousMap.isometryEquivBoundedOfCompact

def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun f => rfl }
#align continuous_map.linear_isometry_bounded_of_compact ContinuousMap.linearIsometryBoundedOfCompact

def evalCLM (x : α) : C(α, E) →L[𝕜] E :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.eval_clm ContinuousMap.evalCLM

def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.choose (uniform_continuity f ε h)
#align continuous_map.modulus ContinuousMap.modulus

def ContinuousLinearMap.compLeftContinuousCompact (g : β →L[𝕜] γ) :
    C(X, β) →L[𝕜] C(X, γ) :=
  (linearIsometryBoundedOfCompact X γ 𝕜).symm.toLinearIsometry.toContinuousLinearMap.comp <|
    (g.compLeftContinuousBounded X).comp <|
      (linearIsometryBoundedOfCompact X β 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_linear_map.comp_left_continuous_compact ContinuousLinearMap.compLeftContinuousCompact

def compRightContinuousMap {X Y : Type*} (T : Type*) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MetricSpace T] (f : C(X, Y)) : C(C(Y, T), C(X, T)) where
  toFun g := g.comp f
  continuous_toFun := by
    refine' Metric.continuous_iff.mpr _
    intro g ε ε_pos
    refine' ⟨ε, ε_pos, fun g' h => _⟩
    rw [ContinuousMap.dist_lt_iff ε_pos] at h ⊢
    exact fun x => h (f x)
#align continuous_map.comp_right_continuous_map ContinuousMap.compRightContinuousMap

def compRightHomeomorph {X Y : Type*} (T : Type*) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MetricSpace T] (f : X ≃ₜ Y) : C(Y, T) ≃ₜ C(X, T) where
  toFun := compRightContinuousMap T f.toContinuousMap
  invFun := compRightContinuousMap T f.symm.toContinuousMap
  left_inv g := ext fun _ => congr_arg g (f.apply_symm_apply _)
  right_inv g := ext fun _ => congr_arg g (f.symm_apply_apply _)
#align continuous_map.comp_right_homeomorph ContinuousMap.compRightHomeomorph