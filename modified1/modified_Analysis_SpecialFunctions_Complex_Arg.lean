def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / abs x)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / abs x) + π else Real.arcsin ((-x).im / abs x) - π
#align complex.arg Complex.arg