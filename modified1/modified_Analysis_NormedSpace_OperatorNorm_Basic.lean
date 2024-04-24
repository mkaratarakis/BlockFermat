def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }
#align linear_isometry.to_span_singleton LinearIsometry.toSpanSingleton

def opNorm (f : E →SL[σ₁₂] F) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
#align continuous_linear_map.op_norm ContinuousLinearMap.opNorm

def (f : E →SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl
#align continuous_linear_map.norm_def ContinuousLinearMap.norm_def

def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F) |>.uniformity_eq_of_hasBasis
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices ∀ f : E →SL[σ₁₂] F, (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) → ‖f‖ ≤ ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx ↦ ?_
    exact (hf x hx.le).trans ((div_le_iff' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm
#align continuous_linear_map.to_pseudo_metric_space ContinuousLinearMap.toPseudoMetricSpace

def restrictScalarsIsometry : (E →L[𝕜] Fₗ) →ₗᵢ[𝕜''] E →L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩
#align continuous_linear_map.restrict_scalars_isometry ContinuousLinearMap.restrictScalarsIsometry

def restrictScalarsL : (E →L[𝕜] Fₗ) →L[𝕜''] E →L[𝕜'] Fₗ :=
  (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toContinuousLinearMap
#align continuous_linear_map.restrict_scalarsL ContinuousLinearMap.restrictScalarsL

structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `F`. -/
protected def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F) |>.uniformity_eq_of_hasBasis
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices ∀ f : E →SL[σ₁₂] F, (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) → ‖f‖ ≤ ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx ↦ ?_
    exact (hf x hx.le).trans ((div_le_iff' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm
#align continuous_linear_map.to_pseudo_metric_space ContinuousLinearMap.toPseudoMetricSpace