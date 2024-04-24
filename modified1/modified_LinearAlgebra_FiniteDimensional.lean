def FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V
#align finite_dimensional FiniteDimensional

def fintypeOfFintype [Fintype K] [FiniteDimensional K V] : Fintype V :=
  Module.fintypeOfFintype (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))
#align finite_dimensional.fintype_of_fintype FiniteDimensional.fintypeOfFintype

def fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) :
    Fintype ι :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis b)
#align finite_dimensional.fintype_basis_index FiniteDimensional.fintypeBasisIndex

def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
    (hv : v ≠ 0) : Basis ι K V :=
  let b := FiniteDimensional.basisUnique ι h
  let h : b.repr v default ≠ 0 := mt FiniteDimensional.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_smul' := by simp [mul_div]
      left_inv := fun w => by
        apply_fun b.repr using b.repr.toEquiv.injective
        apply_fun Equiv.finsuppUnique
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          smul_eq_mul, Pi.smul_apply, Equiv.finsuppUnique_apply]
        exact div_mul_cancel₀ _ h
      right_inv := fun f => by
        ext
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply]
        exact mul_div_cancel_right₀ _ h }
#align finite_dimensional.basis_singleton FiniteDimensional.basisSingleton

def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₁, Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₂])
#align finite_dimensional.linear_equiv.quot_equiv_of_equiv FiniteDimensional.LinearEquiv.quotEquivOfEquiv

def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _ <|
    add_right_cancel <| by
      rw [Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f, add_comm,
        Submodule.finrank_quotient_add_finrank]
#align finite_dimensional.linear_equiv.quot_equiv_of_quot_equiv FiniteDimensional.LinearEquiv.quotEquivOfQuotEquiv

def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩
#align linear_equiv.of_injective_endo LinearEquiv.ofInjectiveEndo

def basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
    (hV : finrank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _
#align basis_of_finrank_zero basisOfFinrankZero

def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V →ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩
#align linear_map.linear_equiv_of_injective LinearMap.linearEquivOfInjective

def divisionRingOfFiniteDimensional (F K : Type*) [Field F] [h : Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : DivisionRing K :=
  { ‹IsDomain K› with
    toRing := h
    inv := fun x =>
      letI := Classical.decEq K
      if H : x = 0 then 0 else Classical.choose <| FiniteDimensional.exists_mul_eq_one F H
    mul_inv_cancel := fun x hx =>
      show x * dite _ (h := _) _ = _ by
        rw [dif_neg hx]
        exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
    inv_zero := dif_pos rfl
    qsmul := qsmulRec _ }
#align division_ring_of_finite_dimensional divisionRingOfFiniteDimensional

def fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K with
    toCommRing := h }
#align field_of_finite_dimensional fieldOfFiniteDimensional

def basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    Basis ι K V :=
  Basis.mk lin_ind <| (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge
#align basis_of_linear_independent_of_card_eq_finrank basisOfLinearIndependentOfCardEqFinrank

def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _
    ⟨(⟨hs.choose, hs.choose_spec⟩ : s)⟩ _ _ lin_ind (_root_.trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_linear_independent_of_card_eq_finrank finsetBasisOfLinearIndependentOfCardEqFinrank

def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)
#align set_basis_of_linear_independent_of_card_eq_finrank setBasisOfLinearIndependentOfCardEqFinrank