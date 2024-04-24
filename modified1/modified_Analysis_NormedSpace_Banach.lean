def ContinuousLinearEquiv.toNonlinearRightInverse (f : E ≃SL[σ] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F) where
  toFun := f.invFun
  nnnorm := ‖(f.symm : F →SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F →SL[σ'] E) _
  right_inv' := f.apply_symm_apply
#align continuous_linear_equiv.to_nonlinear_right_inverse ContinuousLinearEquiv.toNonlinearRightInverse

def nonlinearRightInverseOfSurjective (f : E →SL[σ] F)
  (hsurj : LinearMap.range f = ⊤) : NonlinearRightInverse f :=
  Classical.choose (exists_nonlinearRightInverse_of_surjective f hsurj)
#align continuous_linear_map.nonlinear_right_inverse_of_surjective ContinuousLinearMap.nonlinearRightInverseOfSurjective

def toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : E ≃SL[σ] F :=
  { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }
#align linear_equiv.to_continuous_linear_equiv_of_continuous LinearEquiv.toContinuousLinearEquivOfContinuous

def equivRange (f : E →SL[σ] F) (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] LinearMap.range f :=
  have : CompleteSpace (LinearMap.range f) := hclo.completeSpace_coe
  LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj) <|
    (f.continuous.codRestrict fun x ↦ LinearMap.mem_range_self f x).congr fun _ ↦ rfl

@[simp]
theorem coe_linearMap_equivRange (f : E →SL[σ] F) (hinj : Injective f) (hclo : IsClosed (range f)) :
    f.equivRange hinj hclo = f.rangeRestrict :=
  rfl

@[simp]
theorem coe_equivRange (f : E →SL[σ] F) (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo : E → LinearMap.range f) = f.rangeRestrict :=
  rfl

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable [CompleteSpace E]

/-- Convert a bijective continuous linear map `f : E →SL[σ] F` from a Banach space to a normed space
to a continuous linear equivalence. -/
noncomputable def ofBijective (f : E →SL[σ] F) (hinj : ker f = ⊥) (hsurj : LinearMap.range f = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective ↑f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: added `by convert`
    (by convert f.continuous)
#align continuous_linear_equiv.of_bijective ContinuousLinearEquiv.ofBijective

def coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl (LinearMap.range f) G) [CompleteSpace G] (hker : ker f = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · rw [hker, Submodule.ker_subtypeL, Submodule.prod_bot]
      · rw [Submodule.range_subtypeL]
        exact h.disjoint)
    (by simp only [range_coprod, Submodule.range_subtypeL, h.sup_eq_top])
set_option linter.uppercaseLean3 false in
#align continuous_linear_map.coprod_subtypeL_equiv_of_is_compl ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl

def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_isClosed_graph hg
#align continuous_linear_map.of_is_closed_graph ContinuousLinearMap.ofIsClosedGraph

def ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg
#align continuous_linear_map.of_seq_closed_graph ContinuousLinearMap.ofSeqClosedGraph

structure NonlinearRightInverse where
  toFun : F → E
  nnnorm : ℝ≥0
  bound' : ∀ y, ‖toFun y‖ ≤ nnnorm * ‖y‖
  right_inv' : ∀ y, f (toFun y) = y
#align continuous_linear_map.nonlinear_right_inverse ContinuousLinearMap.NonlinearRightInverse