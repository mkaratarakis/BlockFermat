def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
#align ring_hom.finite_type RingHom.FiniteType

def FiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FiniteType
#align alg_hom.finite_type AlgHom.FiniteType