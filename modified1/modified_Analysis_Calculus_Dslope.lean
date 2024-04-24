def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E :=
  update (slope f a) a (deriv f a)
#align dslope dslope