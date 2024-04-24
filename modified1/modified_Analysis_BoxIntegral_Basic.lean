def integralSum (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) : F :=
  ∑ J in π.boxes, vol J (f (π.tag J))
#align box_integral.integral_sum BoxIntegral.integralSum

def HasIntegral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (y : F) :
    Prop :=
  Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)
#align box_integral.has_integral BoxIntegral.HasIntegral

def Integrable (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  ∃ y, HasIntegral I l f vol y
#align box_integral.integrable BoxIntegral.Integrable

def integral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  if h : Integrable I l f vol then h.choose else 0
#align box_integral.integral BoxIntegral.integral

def convergenceR (h : Integrable I l f vol) (ε : ℝ) : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ) :=
  if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩
#align box_integral.integrable.convergence_r BoxIntegral.Integrable.convergenceR

def toBoxAdditive (h : Integrable I l f vol) : ι →ᵇᵃ[I] F where
  toFun J := integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ, Prepartition.top_boxes,
      sum_singleton]
#align box_integral.integrable.to_box_additive BoxIntegral.Integrable.toBoxAdditive