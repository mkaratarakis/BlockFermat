def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y))
    (hfc : Continuous f) : P →ᵃ[ℝ] Q :=
  let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
    ((AffineEquiv.vaddConst ℝ (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst ℝ c) (by simp)
    fun x y => by -- Porting note: was `by simp [h]`
      simp only [c, Function.comp_apply, AffineEquiv.vaddConst_apply,
        AffineEquiv.vaddConst_symm_apply]
      conv_lhs => rw [(midpoint_self ℝ (Classical.arbitrary P)).symm, midpoint_vadd_midpoint, h, h,
          midpoint_vsub_midpoint]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    c fun p => by simp
#align affine_map.of_map_midpoint AffineMap.ofMapMidpoint