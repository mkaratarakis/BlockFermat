def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_inner (𝕜 := 𝕜) x, hx, map_zero] }
#align inner_product_space.to_core InnerProductSpace.toCore

def toInner' : Inner 𝕜 F :=
  c.toInner
#align inner_product_space.core.to_has_inner' InnerProductSpace.Core.toInner'

def normSq (x : F) :=
  reK ⟪x, x⟫
#align inner_product_space.core.norm_sq InnerProductSpace.Core.normSq

def toNorm : Norm F where norm x := √(re ⟪x, x⟫)
#align inner_product_space.core.to_has_norm InnerProductSpace.Core.toNorm

def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun x hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }
#align inner_product_space.core.to_normed_add_comm_group InnerProductSpace.Core.toNormedAddCommGroup

def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
      ofReal_re]
    · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    · positivity
#align inner_product_space.core.to_normed_space InnerProductSpace.Core.toNormedSpace

def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (c : InnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := @InnerProductSpace.Core.toNormedSpace 𝕜 F _ _ _ c
  { c with
    norm_sq_eq_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (c.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (c.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }
#align inner_product_space.of_core InnerProductSpace.ofCore

def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _
#align sesq_form_of_inner sesqFormOfInner

def bilinFormOfRealInner : BilinForm ℝ F := sesqFormOfInner.flip
#align bilin_form_of_real_inner bilinFormOfRealInner

def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0
#align orthonormal Orthonormal

def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq
#align basis_of_orthonormal_of_card_eq_finrank basisOfOrthonormalOfCardEqFinrank

def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_inner 𝕜, h]⟩
#align linear_map.isometry_of_inner LinearMap.isometryOfInner

def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩
#align linear_equiv.isometry_of_inner LinearEquiv.isometryOfInner

def LinearMap.isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    classical rw [← v.total_repr x, ← v.total_repr y, Finsupp.apply_total, Finsupp.apply_total,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_map.isometry_of_orthonormal LinearMap.isometryOfOrthonormal

def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    classical rw [← v.total_repr x, ← v.total_repr y, ← LinearEquiv.coe_coe f, Finsupp.apply_total,
      Finsupp.apply_total, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_equiv.isometry_of_orthonormal LinearEquiv.isometryOfOrthonormal

def Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
  (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      classical exact hv'.comp _ e.injective)
#align orthonormal.equiv Orthonormal.equiv

def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _
#align innerₛₗ innerₛₗ

def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ

@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w

variable {F}

@[simp] lemma innerₗ_apply (v w : F) : innerₗ F v w = ⟪v, w⟫_ℝ := rfl

/-- The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp. `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply]
set_option linter.uppercaseLean3 false in
#align innerSL innerSL

def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)
set_option linter.uppercaseLean3 false in
#align innerSL_flip innerSLFlip

def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)
#align continuous_linear_map.to_sesq_form ContinuousLinearMap.toSesqForm

def OrthogonalFamily (G : ι → Type*) [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  Pairwise fun i j => ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0
#align orthogonal_family OrthogonalFamily

def Inner.rclikeToReal : Inner ℝ E where inner x y := re ⟪x, y⟫
#align has_inner.is_R_or_C_to_real Inner.rclikeToReal

def InnerProductSpace.rclikeToReal : InnerProductSpace ℝ E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜
      E with
    norm_sq_eq_inner := norm_sq_eq_inner
    conj_symm := fun x y => inner_re_symm _ _
    add_left := fun x y z => by
      change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫
      simp only [inner_add_left, map_add]
    smul_left := fun x y r => by
      change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫
      simp only [inner_smul_left, conj_ofReal, re_ofReal_mul] }
#align inner_product_space.is_R_or_C_to_real InnerProductSpace.rclikeToReal

def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫
#align continuous_linear_map.re_apply_inner_self ContinuousLinearMap.reApplyInnerSelf

def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]
#align continuous_linear_map.re_apply_inner_self_smul ContinuousLinearMap.reApplyInnerSelf_smul

structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/


/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `InnerProductSpace` instance in `InnerProductSpace.ofCore`. -/
-- @[nolint HasNonemptyInstance] porting note: I don't think we have this linter anymore
structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
#align inner_product_space.core InnerProductSpace.Core

structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

/-- Define `InnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`InnerProductSpace.Core` for `InnerProductSpace`s. Note that the `Norm` instance provided by
`InnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_inner (𝕜 := 𝕜) x, hx, map_zero] }
#align inner_product_space.to_core InnerProductSpace.toCore

structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simpa only [inner_zero_left, map_zero, zero_mul, norm_zero] using le_rfl
  · have hx' : 0 < normSqF x := inner_self_nonneg.lt_of_ne' (mt normSq_eq_zero.1 hx)
    rw [← sub_nonneg, ← mul_nonneg_iff_right_nonneg_of_pos hx', ← normSq, ← normSq,
      norm_inner_symm y, ← sq, ← cauchy_schwarz_aux]
    exact inner_self_nonneg
#align inner_product_space.core.inner_mul_inner_self_le InnerProductSpace.Core.inner_mul_inner_self_le

structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun x hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }
#align inner_product_space.core.to_normed_add_comm_group InnerProductSpace.Core.toNormedAddCommGroup

structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
      ofReal_re]
    · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    · positivity
#align inner_product_space.core.to_normed_space InnerProductSpace.Core.toNormedSpace

structure on a space, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroup`. -/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (c : InnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := @InnerProductSpace.Core.toNormedSpace 𝕜 F _ _ _ c
  { c with
    norm_sq_eq_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (c.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (c.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }
#align inner_product_space.of_core InnerProductSpace.ofCore

structure on subspaces -/


/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  { Submodule.normedSpace W with
    inner := fun x y => ⟪(x : E), (y : E)⟫
    conj_symm := fun _ _ => inner_conj_symm _ _
    norm_sq_eq_inner := fun x => norm_sq_eq_inner (x : E)
    add_left := fun _ _ _ => inner_add_left _ _ _
    smul_left := fun _ _ _ => inner_smul_left _ _ _ }
#align submodule.inner_product_space Submodule.innerProductSpace

structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`PiLp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def OrthogonalFamily (G : ι → Type*) [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  Pairwise fun i j => ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0
#align orthogonal_family OrthogonalFamily

structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def InnerProductSpace.rclikeToReal : InnerProductSpace ℝ E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜
      E with
    norm_sq_eq_inner := norm_sq_eq_inner
    conj_symm := fun x y => inner_re_symm _ _
    add_left := fun x y z => by
      change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫
      simp only [inner_add_left, map_add]
    smul_left := fun x y r => by
      change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫
      simp only [inner_smul_left, conj_ofReal, re_ofReal_mul] }
#align inner_product_space.is_R_or_C_to_real InnerProductSpace.rclikeToReal