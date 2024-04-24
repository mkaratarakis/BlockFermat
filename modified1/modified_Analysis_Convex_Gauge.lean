def gauge (s : Set E) (x : E) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ x ∈ r • s }
#align gauge gauge

def : gauge s x = sInf ({ r ∈ Set.Ioi (0 : ℝ) | x ∈ r • s }) :=
  rfl
#align gauge_def gauge_def

def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)
#align gauge_seminorm gaugeSeminorm