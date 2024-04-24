def neTopHomeomorphNNReal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 where
  toEquiv := neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _
#align ennreal.ne_top_homeomorph_nnreal ENNReal.neTopHomeomorphNNReal

def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine' (Homeomorph.setCongr _).trans neTopHomeomorphNNReal
  simp only [mem_setOf_eq, lt_top_iff_ne_top]
#align ennreal.lt_top_homeomorph_nnreal ENNReal.ltTopHomeomorphNNReal

def metricSpaceEMetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (ball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball
#align metric_space_emetric_ball metricSpaceEMetricBall