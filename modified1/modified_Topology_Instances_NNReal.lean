def _root_.ContinuousMap.realToNNReal : C(ℝ, ℝ≥0) :=
  .mk Real.toNNReal continuous_real_toNNReal

theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ) :=
  continuous_subtype_val
#align nnreal.continuous_coe NNReal.continuous_coe

def _root_.ContinuousMap.coeNNRealReal : C(ℝ≥0, ℝ) :=
  ⟨(↑), continuous_coe⟩
#align continuous_map.coe_nnreal_real ContinuousMap.coeNNRealReal

def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (fun x ↦ x ^ n) (fun x y h =>
      pow_left_strictMonoOn hn (zero_le x) (zero_le y) h) <|
    (continuous_id.pow _).surjective (tendsto_pow_atTop hn) <| by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]
#align nnreal.pow_order_iso NNReal.powOrderIso