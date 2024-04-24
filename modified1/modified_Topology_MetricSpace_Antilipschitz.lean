def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)
#align antilipschitz_with AntilipschitzWith

def k (_hf : AntilipschitzWith K f) : ℝ≥0 := K
set_option linter.uppercaseLean3 false in
#align antilipschitz_with.K AntilipschitzWith.k