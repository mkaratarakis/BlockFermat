def primeSpectrumProdOfSum : Sum (PrimeSpectrum R) (PrimeSpectrum S) → PrimeSpectrum (R × S)
  | Sum.inl ⟨I, _⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrime_ideal_prod_top⟩
  | Sum.inr ⟨J, _⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrime_ideal_prod_top'⟩
#align prime_spectrum.prime_spectrum_prod_of_sum PrimeSpectrum.primeSpectrumProdOfSum

def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ Sum (PrimeSpectrum R) (PrimeSpectrum S) :=
  Equiv.symm <|
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod.ext_iff, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases (Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)
#align prime_spectrum.prime_spectrum_prod PrimeSpectrum.primeSpectrumProd

def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }
#align prime_spectrum.zero_locus PrimeSpectrum.zeroLocus

def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ (x : PrimeSpectrum R) (_ : x ∈ t), x.asIdeal
#align prime_spectrum.vanishing_ideal PrimeSpectrum.vanishingIdeal

def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm
#align prime_spectrum.closeds_embedding PrimeSpectrum.closedsEmbedding

def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R) where
  toFun y := ⟨Ideal.comap f y.asIdeal, inferInstance⟩
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_comap_zeroLocus_aux f s⟩
#align prime_spectrum.comap PrimeSpectrum.comap

def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩
#align prime_spectrum.basic_open PrimeSpectrum.basicOpen

def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm
#align prime_spectrum.nhds_order_embedding PrimeSpectrum.nhdsOrderEmbedding

def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal →+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes, ← asIdeal_le_asIdeal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a ∈ x.asIdeal.primeCompl from h ha⟩ : _))
#align prime_spectrum.localization_map_of_specializes PrimeSpectrum.localizationMapOfSpecializes

def pointsEquivIrreducibleCloseds :
    PrimeSpectrum R ≃o {s : Set (PrimeSpectrum R) | IsIrreducible s ∧ IsClosed s}ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

section LocalizationAtMinimal

variable {I : Ideal R} [hI : I.IsPrime]

/--
Localizations at minimal primes have single-point prime spectra.
-/
def primeSpectrum_unique_of_localization_at_minimal (h : I ∈ minimalPrimes R) :
    Unique (PrimeSpectrum (Localization.AtPrime I)) where
  default :=
    ⟨LocalRing.maximalIdeal (Localization I.primeCompl),
    (LocalRing.maximalIdeal.isMaximal _).isPrime⟩
  uniq x := PrimeSpectrum.ext _ _ (Localization.AtPrime.prime_unique_of_minimal h x.asIdeal)

end LocalizationAtMinimal

end CommSemiRing

end PrimeSpectrum

section CommSemiring
variable [CommSemiring R]

open PrimeSpectrum in
/--
[Stacks: Lemma 00ES (3)](https://stacks.math.columbia.edu/tag/00ES)
Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` and any
irreducible component is a zero locus of some minimal prime ideal.
-/
protected def minimalPrimes.equivIrreducibleComponents :
    minimalPrimes R ≃o (irreducibleComponents <| PrimeSpectrum R)ᵒᵈ :=
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ ≤ p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x ↦ ⟨x.1, x.2.1⟩, fun x ↦ ⟨x.1, x.2, bot_le⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩
  (e.trans <| PrimeSpectrum.pointsEquivIrreducibleCloseds R).minimalsIsoMaximals.trans
    (OrderIso.setCongr _ _ <| by simp_rw [irreducibleComponents_eq_maximals_closed, and_comm]).dual

namespace PrimeSpectrum

lemma vanishingIdeal_irreducibleComponents :
    vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) =
    minimalPrimes R := by
  rw [irreducibleComponents_eq_maximals_closed, minimalPrimes_eq_minimals, ← minimals_swap,
    ← PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible, image_minimals_of_rel_iff_rel]
  exact fun s t hs _ ↦ vanishingIdeal_anti_mono_iff hs.1

lemma zeroLocus_minimalPrimes :
    zeroLocus ∘ (↑) '' minimalPrimes R =
    irreducibleComponents (PrimeSpectrum R) := by
  rw [← vanishingIdeal_irreducibleComponents, ← Set.image_comp, Set.EqOn.image_eq_self]
  intros s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

variable {R}

lemma vanishingIdeal_mem_minimalPrimes {s : Set (PrimeSpectrum R)} :
    vanishingIdeal s ∈ minimalPrimes R ↔ closure s ∈ irreducibleComponents (PrimeSpectrum R) := by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _

lemma zeroLocus_ideal_mem_irreducibleComponents {I : Ideal R} :
    zeroLocus I ∈ irreducibleComponents (PrimeSpectrum R) ↔ I.radical ∈ minimalPrimes R := by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

end PrimeSpectrum

end CommSemiring

namespace LocalRing

variable [CommSemiring R] [LocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
#align local_ring.closed_point LocalRing.closedPoint

structure PrimeSpectrum [CommSemiring R] where
  asIdeal : Ideal R
  IsPrime : asIdeal.IsPrime
#align prime_spectrum PrimeSpectrum