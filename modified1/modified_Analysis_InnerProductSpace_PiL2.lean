def EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜
#align euclidean_space EuclideanSpace

def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine' LinearEquiv.isometryOfInner (e₂.symm.trans e₁) _
  suffices ∀ (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀)) <;>
      simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp
#align direct_sum.is_internal.isometry_L2_of_orthogonal_family DirectSum.IsInternal.isometryL2OfOrthogonalFamily

def EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι →ₗ[𝕜] 𝕜 :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 𝕜 (ι → 𝕜) : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜)
#align euclidean_space.projₗ EuclideanSpace.projₗ

def EuclideanSpace.proj (i : ι) : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜 :=
  ⟨EuclideanSpace.projₗ i, continuous_apply i⟩
#align euclidean_space.proj EuclideanSpace.proj

def EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι :=
  (WithLp.equiv _ _).symm (Pi.single i a)
#align euclidean_space.single EuclideanSpace.single

def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun b.repr.toLinearEquiv
#align orthonormal_basis.to_basis OrthonormalBasis.toBasis

def map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where
  repr := L.symm.trans b.repr
#align orthonormal_basis.map OrthonormalBasis.map

def _root_.Basis.toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.ofRepr <|
    LinearEquiv.isometryOfInner v.equivFun
      (by
        intro x y
        let p : EuclideanSpace 𝕜 ι := v.equivFun x
        let q : EuclideanSpace 𝕜 ι := v.equivFun y
        have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫ := by
          simp [sum_inner, inner_smul_left, hv.inner_right_fintype]
        convert key
        · rw [← v.equivFun.symm_apply_apply x, v.equivFun_symm_apply]
        · rw [← v.equivFun.symm_apply_apply y, v.equivFun_symm_apply])
#align basis.to_orthonormal_basis Basis.toOrthonormalBasis

def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])
#align orthonormal_basis.mk OrthonormalBasis.mk

def span [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s → ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert orthonormal_span (h.comp ((↑) : s → ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s → ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image, image_eq_range]
        rfl)
  e₀.map φ.symm
#align orthonormal_basis.span OrthonormalBasis.span

def mkOfOrthogonalEqBot (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hon
    (by
      refine' Eq.ge _
      haveI : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      haveI : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)
#align orthonormal_basis.mk_of_orthogonal_eq_bot OrthonormalBasis.mkOfOrthogonalEqBot

def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))
#align orthonormal_basis.reindex OrthonormalBasis.reindex

def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]
theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1 :=
  PiLp.basisFun_apply _ _ _ _

@[simp]
theorem basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i = x i := rfl

theorem basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι := rfl

end EuclideanSpace

instance OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨EuclideanSpace.basisFun ι 𝕜⟩
#align orthonormal_basis.inhabited OrthonormalBasis.instInhabited

def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])
#align complex.orthonormal_basis_one_I Complex.orthonormalBasisOneI

def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm
#align complex.isometry_of_orthonormal Complex.isometryOfOrthonormal

def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι → Type*} [∀ i, Fintype (α i)]
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σi, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by simp)
#align direct_sum.is_internal.collected_orthonormal_basis DirectSum.IsInternal.collectedOrthonormalBasis

def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)
#align std_orthonormal_basis stdOrthonormalBasis

def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    (Σi, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (FiniteDimensional.finrank_eq_card_basis b.toBasis).symm.trans hn
#align direct_sum.is_internal.sigma_orthonormal_basis_index_equiv DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv

def DirectSum.IsInternal.subordinateOrthonormalBasis
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')
#align direct_sum.is_internal.subordinate_orthonormal_basis DirectSum.IsInternal.subordinateOrthonormalBasis

def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1
#align direct_sum.is_internal.subordinate_orthonormal_basis_index DirectSum.IsInternal.subordinateOrthonormalBasisIndex

def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  -- Porting note: was `attribute [local instance] FiniteDimensional.of_fact_finrank_eq_succ`
  haveI : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
  (stdOrthonormalBasis _ _).reindex <| finCongr <| finrank_orthogonal_span_singleton hv
#align orthonormal_basis.from_orthogonal_span_singleton OrthonormalBasis.fromOrthogonalSpanSingleton

def LinearIsometry.extend (L : S →ₗᵢ[𝕜] V) : V →ₗᵢ[𝕜] V := by
  -- Build an isometry from Sᗮ to L(S)ᗮ through `EuclideanSpace`
  let d := finrank 𝕜 Sᗮ
  let LS := LinearMap.range L.toLinearMap
  have E : Sᗮ ≃ₗᵢ[𝕜] LSᗮ := by
    have dim_LS_perp : finrank 𝕜 LSᗮ = d :=
      calc
        finrank 𝕜 LSᗮ = finrank 𝕜 V - finrank 𝕜 LS := by
          simp only [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
        _ = finrank 𝕜 V - finrank 𝕜 S := by simp only [LinearMap.finrank_range_of_inj L.injective]
        _ = finrank 𝕜 Sᗮ := by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]

    exact
      (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
        ((stdOrthonormalBasis 𝕜 LSᗮ).reindex <| finCongr dim_LS_perp).repr.symm
  let L3 := LSᗮ.subtypeₗᵢ.comp E.toLinearIsometry
  -- Project onto S and Sᗮ
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let p1 := (orthogonalProjection S).toLinearMap
  let p2 := (orthogonalProjection Sᗮ).toLinearMap
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.toLinearMap.comp p1 + L3.toLinearMap.comp p2
  -- Prove that M is an isometry
  have M_norm_map : ∀ x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) ∈ LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) ∈ (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LinearIsometry.coe_comp, Function.comp_apply, Submodule.coe_subtypeₗᵢ, ←
          Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map, _root_.add_left_inj, mul_eq_mul_left_iff,
      norm_eq_zero, true_or_iff, eq_self_iff_true, ContinuousLinearMap.coe_coe, Submodule.coe_norm,
      Submodule.coe_eq_zero]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }
#align linear_isometry.extend LinearIsometry.extend

def toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  Matrix.toLin' ≪≫ₗ
    LinearEquiv.arrowCongr (WithLp.linearEquiv _ 𝕜 (n → 𝕜)).symm
      (WithLp.linearEquiv _ 𝕜 (m → 𝕜)).symm
#align matrix.to_euclidean_lin Matrix.toEuclideanLin

structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `PiLp 2`.

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `OrthonormalBasis 𝕜 ι E` as a linear isometric equivalence
between `E` and `EuclideanSpace 𝕜 ι`. Then `stdOrthonormalBasis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `Basis.toOrthonormalBasis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the whole sum in `DirectSum.IsInternal.subordinateOrthonormalBasis`. In
the last section, various properties of matrices are explored.

## Main definitions

structure OrthonormalBasis where ofRepr ::
  /-- Linear isometry between `E` and `EuclideanSpace 𝕜 ι` representing the orthonormal basis. -/
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι
#align orthonormal_basis OrthonormalBasis