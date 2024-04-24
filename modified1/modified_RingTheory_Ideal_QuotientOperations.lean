def kerLift : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun _ => f.mem_ker.mp
#align ring_hom.ker_lift RingHom.kerLift

def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :
    R ⧸ ker f ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }
#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverse

def _root_.RingEquiv.quotientBot : R ⧸ (⊥ : Ideal R) ≃+* R :=
  (Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans <|
    quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ ↦ rfl

/-- The **first isomorphism theorem** for commutative rings, surjective case. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjective

def quotientKerEquivRangeS (f : R →+* S) : R ⧸ ker f ≃+* f.rangeS :=
  (Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans <|
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

variable {S : Type v} [Ring S] (f : R →+* S)

/-- The **first isomorphism theorem** for commutative rings (`RingHom.range` version). -/
noncomputable def quotientKerEquivRange (f : R →+* S) : R ⧸ ker f ≃+* f.range :=
  (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans <|
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

end RingHom

namespace Ideal
open Function RingHom

variable {R : Type u} {S : Type v} {F : Type w} [CommRing R] [Semiring S]

@[simp]
theorem map_quotient_self (I : Ideal R) : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
    -- Porting note: Lean can't infer `Module (R ⧸ I) (R ⧸ I)` on its own
      (@Submodule.mem_bot (R ⧸ I) _ _ _ Semiring.toModule _).2 <|
          Ideal.Quotient.eq_zero_iff_mem.2 hx
#align ideal.map_quotient_self Ideal.map_quotient_self

def quotientInfToPiQuotient (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

lemma quotientInfToPiQuotient_mk (I : ι → Ideal R) (x : R) :
    quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
rfl

lemma quotientInfToPiQuotient_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
rfl

lemma quotientInfToPiQuotient_inj (I : ι → Ideal R) : Injective (quotientInfToPiQuotient I) := by
  rw [quotientInfToPiQuotient, injective_lift_iff, ker_Pi_Quotient_mk]

lemma quotientInfToPiQuotient_surj [Finite ι] {I : ι → Ideal R}
    (hI : Pairwise fun i j => IsCoprime (I i) (I j)) : Surjective (quotientInfToPiQuotient I) := by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i ↦ mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intros j hj
      exact hI (by simpa [ne_comm, isCoprime_iff_add] using hj)
    rcases isCoprime_iff_exists.mp (isCoprime_biInf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i*e i)
  ext i
  rw [quotientInfToPiQuotient_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotientInfRingEquivPiQuotient [Finite ι] (f : ι → Ideal R)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }
#align ideal.quotient_inf_ring_equiv_pi_quotient Ideal.quotientInfRingEquivPiQuotient

def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J :=
  let f : Fin 2 → Ideal R := ![I, J]
  have hf : Pairwise fun i j => IsCoprime (f i) (f j) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
  (Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans <|
            (Ideal.quotientInfRingEquivPiQuotient f hf).trans <| RingEquiv.piFinTwo fun i => R ⧸ f i
#align ideal.quotient_inf_equiv_quotient_prod Ideal.quotientInfEquivQuotientProd

def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra

def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
#align ideal.quotient.mkₐ Ideal.Quotient.mkₐ

def Quotient.liftₐ (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = algebraMap A (A ⧸ I) (algebraMap R₁ A r) := by
        simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
      rw [this, Ideal.Quotient.algebraMap_eq, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }
#align ideal.quotient.liftₐ Ideal.Quotient.liftₐ

def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ (RingHom.ker f) →ₐ[R₁] B :=
  AlgHom.mk' (RingHom.kerLift (f : A →+* B)) fun _ _ => KerLift.map_smul f _ _
#align ideal.ker_lift_alg Ideal.kerLiftAlg

def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ RingHom.ker f) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }
#align ideal.quotient_ker_alg_equiv_of_right_inverse Ideal.quotientKerAlgEquivOfRightInverse

def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ (RingHom.ker f)) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
#align ideal.quotient_ker_alg_equiv_of_surjective Ideal.quotientKerAlgEquivOfSurjective

def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha
#align ideal.quotient_map Ideal.quotientMap

def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
    R ⧸ I ≃+* S ⧸ J :=
  {
    quotientMap J (↑f) (by
      rw [hIJ]
      exact le_comap_map)
  with
    invFun :=
      quotientMap I (↑f.symm)
        (by
          rw [hIJ]
          exact le_of_eq (map_comap_of_equiv I f))
    left_inv := by
      rintro ⟨r⟩
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
        quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    right_inv := by
      rintro ⟨s⟩
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
        quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] }
#align ideal.quotient_equiv Ideal.quotientEquiv

def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }
#align ideal.quotient_mapₐ Ideal.quotientMapₐ

def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' := fun r => by
      -- Porting note: Needed to add the below lemma because Equivs coerce weird
      have : ∀ (e : RingEquiv (A ⧸ I) (B ⧸ J)), Equiv.toFun e.toEquiv = DFunLike.coe e :=
        fun _ ↦ rfl
      rw [this]
      simp only [quotientEquiv_apply, RingHom.toFun_eq_coe, quotientMap_algebraMap,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, Quotient.mk_algebraMap]}
#align ideal.quotient_equiv_alg Ideal.quotientEquivAlg

def quotientEquivAlgOfEq {I J : Ideal A} (h : I = J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
#align ideal.quotient_equiv_alg_of_eq Ideal.quotientEquivAlgOfEq

def quotientKerEquivRange
  {A B : Type*} [CommRing A] [Algebra R A] [Semiring B] [Algebra R B]
  (f : A →ₐ[R] B) :
  (A ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
  (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

end QuotientAlgebra

end Ideal

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor I (I ⊔ J) le_sup_left
#align double_quot.quot_left_to_quot_sup DoubleQuot.quotLeftToQuotSup

def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le
#align double_quot.quot_quot_to_quot_sup DoubleQuot.quotQuotToQuotSup

def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)
#align double_quot.quot_quot_mk DoubleQuot.quotQuotMk

def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le
#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMk

def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
#align double_quot.quot_quot_equiv_quot_sup DoubleQuot.quotQuotEquivQuotSup

def quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
    (R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J) :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm
#align double_quot.quot_quot_equiv_comm DoubleQuot.quotQuotEquivComm

def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)
#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLE

def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl
#align double_quot.quot_left_to_quot_supₐ DoubleQuot.quotLeftToQuotSupₐ

def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_to_quot_supₐ DoubleQuot.quotQuotToQuotSupₐ

def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (quotQuotMk I J) fun _ => rfl
#align double_quot.quot_quot_mkₐ DoubleQuot.quotQuotMkₐ

def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl
#align double_quot.lift_sup_quot_quot_mkₐ DoubleQuot.liftSupQuotQuotMkₐ

def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_supₐ DoubleQuot.quotQuotEquivQuotSupₐ

def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (Quotient.mkₐ R J) :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivComm I J) fun _ => rfl
#align double_quot.quot_quot_equiv_commₐ DoubleQuot.quotQuotEquivCommₐ

def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotOfLE h) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ DoubleQuot.quotQuotEquivQuotOfLEₐ

structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  { toRingHom := (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
    smul_def' := fun _ x =>
      Quotient.inductionOn' x fun _ =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra