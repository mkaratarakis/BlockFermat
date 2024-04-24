def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)
#align complex.equiv_real_prod_clm Complex.equivRealProdCLM

def reCLM : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_abs]
#align complex.re_clm Complex.reCLM

def imCLM : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_abs]
#align complex.im_clm Complex.imCLM

def conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, abs_conj⟩
#align complex.conj_lie Complex.conjLIE

def conjCLE : ℂ ≃L[ℝ] ℂ :=
  conjLIE
#align complex.conj_cle Complex.conjCLE

def ofRealLI : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩
#align complex.of_real_li Complex.ofRealLI

def ofRealCLM : ℝ →L[ℝ] ℂ :=
  ofRealLI.toContinuousLinearMap
#align complex.of_real_clm Complex.ofRealCLM

def _root_.RCLike.complexRingEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃+* ℂ where
  toFun x := RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw [I_sq]
    ring

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
def _root_.RCLike.complexLinearIsometryEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃ₗᵢ[ℝ] ℂ where
  map_smul' _ _ := by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq (by positivity) (by positivity), ← normSq_eq_norm_sq, ← RCLike.normSq_eq_def',
      RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

section ComplexOrder

open ComplexOrder

theorem eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ := by
  lift z to ℝ using hz.2.symm
  rw [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg (id hz.1 : 0 ≤ z)]
#align complex.eq_coe_norm_of_nonneg Complex.eq_coe_norm_of_nonneg

structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

structure of `ℂ`. Notably, in the namespace `Complex`,
it defines functions:

* `reCLM`
* `imCLM`
* `ofRealCLM`
* `conjCLE`

They are bundled versions of the real part, the imaginary part, the embedding of `ℝ` in `ℂ`, and
the complex conjugate as continuous `ℝ`-linear maps. The last two are also bundled as linear
isometries in `ofRealLI` and `conjLIE`.

We also register the fact that `ℂ` is an `RCLike` field.
-/


assert_not_exists Absorbs

noncomputable section

namespace Complex
variable {z : ℂ}

open ComplexConjugate Topology Filter

instance : Norm ℂ :=
  ⟨abs⟩

@[simp]
theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z :=
  rfl
#align complex.norm_eq_abs Complex.norm_eq_abs

structure from `Module.complexToReal` is a normed space. -/
instance (priority := 900) _root_.NormedSpace.complexToReal : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
#align normed_space.complex_to_real NormedSpace.complexToReal

structure from `Algebra.complexToReal` is a normed algebra. -/
instance (priority := 900) _root_.NormedAlgebra.complexToReal {A : Type*} [SeminormedRing A]
    [NormedAlgebra ℂ A] : NormedAlgebra ℝ A :=
  NormedAlgebra.restrictScalars ℝ ℂ A

theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl
#align complex.dist_eq Complex.dist_eq