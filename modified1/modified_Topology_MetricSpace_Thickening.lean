def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E < ENNReal.ofReal δ }
#align metric.thickening Metric.thickening

def cthickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E ≤ ENNReal.ofReal δ }
#align metric.cthickening Metric.cthickening