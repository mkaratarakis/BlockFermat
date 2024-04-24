def toBoxAdditive [Finite ι] (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : ι →ᵇᵃ[⊤] ℝ where
  toFun J := (μ J).toReal
  sum_partition_boxes' J _ π hπ := by rw [← π.measure_iUnion_toReal, hπ.iUnion_eq]
#align measure_theory.measure.to_box_additive MeasureTheory.Measure.toBoxAdditive

def volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : ι →ᵇᵃ E →L[ℝ] E :=
  (volume : Measure (ι → ℝ)).toBoxAdditive.toSMul
#align box_integral.box_additive_map.volume BoxIntegral.BoxAdditiveMap.volume