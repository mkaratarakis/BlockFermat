def toSpanNonzeroSingleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)
#align continuous_linear_equiv.to_span_nonzero_singleton ContinuousLinearEquiv.toSpanNonzeroSingleton

def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 :=
  (toSpanNonzeroSingleton 𝕜 x h).symm
#align continuous_linear_equiv.coord ContinuousLinearEquiv.coord