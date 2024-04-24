def infEdist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y
#align emetric.inf_edist EMetric.infEdist

def hausdorffEdist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEdist x t) ⊔ ⨆ y ∈ t, infEdist y s
#align emetric.Hausdorff_edist EMetric.hausdorffEdist

def EMetric.hausdorffEdist_def

section HausdorffEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t u : Set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes. -/
@[simp]
theorem hausdorffEdist_self : hausdorffEdist s s = 0 := by
  simp only [hausdorffEdist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEdist_zero_of_mem hx
#align emetric.Hausdorff_edist_self EMetric.hausdorffEdist_self

def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEdist x s)
#align metric.inf_dist Metric.infDist

def infNndist (x : α) (s : Set α) : ℝ≥0 :=
  ENNReal.toNNReal (infEdist x s)
#align metric.inf_nndist Metric.infNndist

def hausdorffDist (s t : Set α) : ℝ :=
  ENNReal.toReal (hausdorffEdist s t)
#align metric.Hausdorff_dist Metric.hausdorffDist