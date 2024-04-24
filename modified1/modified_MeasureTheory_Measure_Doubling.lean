def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ
#align is_unif_loc_doubling_measure.doubling_constant IsUnifLocDoublingMeasure.doublingConstant

def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1
#align is_unif_loc_doubling_measure.scaling_constant_of IsUnifLocDoublingMeasure.scalingConstantOf

def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose
#align is_unif_loc_doubling_measure.scaling_scale_of IsUnifLocDoublingMeasure.scalingScaleOf