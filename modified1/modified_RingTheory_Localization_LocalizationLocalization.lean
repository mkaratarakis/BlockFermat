def localizationLocalizationSubmodule : Submonoid R :=
  (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)
#align is_localization.localization_localization_submodule IsLocalization.localizationLocalizationSubmodule

def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M))
    [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _
#align is_localization.localization_localization_at_prime_iso_localization IsLocalization.localizationLocalizationAtPrimeIsoLocalization

def localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra
#align is_localization.localization_algebra_of_submonoid_le IsLocalization.localizationAlgebraOfSubmonoidLe

structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable def localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra
#align is_localization.localization_algebra_of_submonoid_le IsLocalization.localizationAlgebraOfSubmonoidLe