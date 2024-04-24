def Quotient.algebraQuotientOfLEComap (h : p ≤ comap f P) : Algebra (R ⧸ p) (S ⧸ P) :=
  RingHom.toAlgebra <| quotientMap _ f h
#align ideal.quotient.algebra_quotient_of_le_comap Ideal.Quotient.algebraQuotientOfLEComap