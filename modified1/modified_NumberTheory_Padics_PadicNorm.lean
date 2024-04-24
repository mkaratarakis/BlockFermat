def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
#align padic_norm padicNorm