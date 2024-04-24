def primeCompl : Submonoid R where
  carrier := (Pᶜ : Set R)
  one_mem' := by convert P.ne_top_iff_one.1 hp.1
  mul_mem' {x y} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny
#align ideal.prime_compl Ideal.primeCompl

def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p ≤ I } :=
  (IsLocalization.orderIsoOfPrime I.primeCompl S).trans <| .setCongr _ _ <| show setOf _ = setOf _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

theorem isUnit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x ∈ I.primeCompl :=
  ⟨fun h hx =>
    (isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top <|
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩
#align is_localization.at_prime.is_unit_to_map_iff IsLocalization.AtPrime.isUnit_to_map_iff

def localRingHom (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I →+* Localization.AtPrime J :=
  IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))
#align localization.local_ring_hom Localization.localRingHom

structure `AtPrime.localRing` -/
theorem AtPrime.map_eq_maximalIdeal :
    Ideal.map (algebraMap R (Localization.AtPrime I)) I =
      LocalRing.maximalIdeal (Localization I.primeCompl) := by
  convert congr_arg (Ideal.map (algebraMap R (Localization.AtPrime I)))
  -- Porting note: `algebraMap R ...` can not be solve by unification
    (AtPrime.comap_maximalIdeal (hI := hI)).symm
  -- Porting note: can not find `hI`
  rw [map_comap I.primeCompl]
#align localization.at_prime.map_eq_maximal_ideal Localization.AtPrime.map_eq_maximalIdeal