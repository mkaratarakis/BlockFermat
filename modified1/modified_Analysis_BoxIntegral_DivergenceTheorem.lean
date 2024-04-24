def ε'0) with ⟨δ, δ0, Hδ⟩
    refine' ⟨δ, δ0, fun J hle hJδ hxJ hJc => _⟩
    simp only [BoxAdditiveMap.volume_apply, Box.volume_apply, dist_eq_norm]
    refine' (norm_volume_sub_integral_face_upper_sub_lower_smul_le _
      (Hc.mono <| Box.le_iff_Icc.1 hle) hxJ ε'0 (fun y hy => Hδ _) (hJc rfl)).trans _
    · exact ⟨hJδ hy, Box.le_iff_Icc.1 hle hy⟩
    · rw [mul_right_comm (2 : ℝ), ← Box.volume_apply]
      exact mul_le_mul_of_nonneg_right hlt.le ENNReal.toReal_nonneg
set_option linter.uppercaseLean3 false in
#align box_integral.has_integral_GP_pderiv BoxIntegral.hasIntegral_GP_pderiv