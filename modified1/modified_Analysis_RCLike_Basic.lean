def r z
#align is_R_or_C.real_smul_eq_coe_mul RCLike.real_smul_eq_coe_mul

def : (Star.star : K → K) = conj :=
  rfl
#align is_R_or_C.star_def RCLike.star_def

def normSq : K →*₀ ℝ where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring
#align is_R_or_C.norm_sq RCLike.normSq

def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z
#align is_R_or_C.norm_sq_eq_def RCLike.norm_sq_eq_def

def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, ofReal_inv, ofReal_pow, mul_inv_cancel]
    simpa
#align is_R_or_C.inv_def RCLike.inv_def

def cauSeqRe (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩
#align is_R_or_C.cau_seq_re RCLike.cauSeqRe

def cauSeqIm (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩
#align is_R_or_C.cau_seq_im RCLike.cauSeqIm

def toStrictOrderedCommRing : StrictOrderedCommRing K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]
  add_le_add_left _ _ := add_le_add_left
  mul_pos z w hz hw := by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]
  mul_comm := by intros; apply ext <;> ring_nf

scoped[ComplexOrder] attribute [instance] RCLike.toStrictOrderedCommRing

theorem toOrderedSMul : OrderedSMul ℝ K :=
  OrderedSMul.mk' fun a b r hab hr => by
    replace hab := hab.le
    rw [RCLike.le_iff_re_im] at hab
    rw [RCLike.le_iff_re_im, smul_re, smul_re, smul_im, smul_im]
    exact hab.imp (fun h => mul_le_mul_of_nonneg_left h hr.le) (congr_arg _)

scoped[ComplexOrder] attribute [instance] RCLike.toOrderedSMul

end Order

open ComplexConjugate

section CleanupLemmas

local notation "reR" => @RCLike.re ℝ _
local notation "imR" => @RCLike.im ℝ _
local notation "IR" => @RCLike.I ℝ _
local notation "normSqR" => @RCLike.normSq ℝ _

@[simp, rclike_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl
#align is_R_or_C.re_to_real RCLike.re_to_real

def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }
#align is_R_or_C.re_lm RCLike.reLm

def reCLM : K →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x
#align is_R_or_C.re_clm RCLike.reCLM

def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }
#align is_R_or_C.im_lm RCLike.imLm

def imCLM : K →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x
#align is_R_or_C.im_clm RCLike.imCLM

def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }
#align is_R_or_C.conj_ae RCLike.conjAe

def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun _ => norm_conj⟩
#align is_R_or_C.conj_lie RCLike.conjLIE

def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _
#align is_R_or_C.conj_cle RCLike.conjCLE

def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K
#align is_R_or_C.of_real_am RCLike.ofRealAm

def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal
#align is_R_or_C.of_real_li RCLike.ofRealLI

def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap
#align is_R_or_C.of_real_clm RCLike.ofRealCLM