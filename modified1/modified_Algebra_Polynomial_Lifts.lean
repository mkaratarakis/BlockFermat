def lifts (f : R →+* S) : Subsemiring S[X] :=
  RingHom.rangeS (mapRingHom f)
#align polynomial.lifts Polynomial.lifts

def liftsRing (f : R →+* S) : Subring S[X] :=
  RingHom.range (mapRingHom f)
#align polynomial.lifts_ring Polynomial.liftsRing

def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] →ₐ[R] S[X] :=
  @aeval _ S[X] _ _ _ (X : S[X])
#align polynomial.map_alg Polynomial.mapAlg