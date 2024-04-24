def Fintype.subtypeProd {E : Type*} {X : Set E} (hX : X.Finite) {L : Type*}
    (F : E → Multiset L) : Fintype (∀ x : X, { l : L // l ∈ F x }) :=
  @Pi.fintype _ _ _ (Finite.fintype hX) _
#align minpoly.fintype.subtype_prod minpoly.Fintype.subtypeProd

def rootsOfMinPolyPiType (φ : E →ₐ[F] K)
    (x : range (FiniteDimensional.finBasis F E : _ → E)) :
    { l : K // l ∈ (minpoly F x.1).aroots K } :=
  ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val),
      ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]⟩
#align minpoly.roots_of_min_poly_pi_type minpoly.rootsOfMinPolyPiType