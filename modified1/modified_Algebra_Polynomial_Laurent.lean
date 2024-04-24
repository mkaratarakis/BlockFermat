def trunc : R[T;T⁻¹] →[R] R[X] :=
--    refine (?_ : R[ℕ] →[R] R[X]).comp ?_
--    · exact ⟨(toFinsuppIso R).symm, by simp⟩
--    · refine ⟨fun r ↦ comapDomain _ r
--        (Set.injOn_of_injective (fun _ _ ↦ Int.ofNat.inj) _), ?_⟩
--      exact fun r f ↦ comapDomain_smul ..
--  ```
--  but it would make sense to bundle the maps better, for a smoother user experience.
--  I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
--  this stage of the Laurent process!
--  This would likely involve adding a `comapDomain` analogue of
--  `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
--  `Polynomial.toFinsuppIso`.
-- Add `degree, int_degree, int_trailing_degree, leading_coeff, trailing_coeff,...`.
-/


open Polynomial BigOperators Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R : Type*}

/-- The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R ℤ
#align laurent_polynomial LaurentPolynomial

def Polynomial.toLaurent [Semiring R] : R[X] →+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R)
#align polynomial.to_laurent Polynomial.toLaurent

def Polynomial.toLaurentAlg [CommSemiring R] : R[X] →ₐ[R] R[T;T⁻¹] := by
  refine' AlgHom.comp _ (toFinsuppIsoAlg R).toAlgHom
  exact mapDomainAlgHom R R Int.ofNatHom
#align polynomial.to_laurent_alg Polynomial.toLaurentAlg

def C : R →+* R[T;T⁻¹] :=
  singleZeroRingHom
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.C LaurentPolynomial.C

def T (n : ℤ) : R[T;T⁻¹] :=
  Finsupp.single n 1
set_option linter.uppercaseLean3 false in
#align laurent_polynomial.T LaurentPolynomial.T

def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comapDomain.addMonoidHom fun _ _ => Int.ofNat.inj
#align laurent_polynomial.trunc LaurentPolynomial.trunc

def degree (f : R[T;T⁻¹]) : WithBot ℤ :=
  f.support.max
#align laurent_polynomial.degree LaurentPolynomial.degree