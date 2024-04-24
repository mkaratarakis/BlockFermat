def stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := stdSimplexEquivIcc ℝ
  continuous_toFun := .subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_subtype_val, continuous_const.sub continuous_subtype_val⟩)

end stdSimplex

/-! ### Topological vector space -/