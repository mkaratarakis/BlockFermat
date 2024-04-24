def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, C r ∣ p → IsUnit r
#align polynomial.is_primitive Polynomial.IsPrimitive

def content (p : R[X]) : R :=
  p.support.gcd p.coeff
#align polynomial.content Polynomial.content

def primPart (p : R[X]) : R[X] :=
  letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)
#align polynomial.prim_part Polynomial.primPart