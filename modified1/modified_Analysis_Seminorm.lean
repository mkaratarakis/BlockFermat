def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]
#align seminorm.of Seminorm.of

def Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ) (map_zero : f 0 = 0)
    (add_le : ∀ x y, f (x + y) ≤ f x + f y) (smul_le : ∀ (r : 𝕜) (x), f (r • x) ≤ ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x => by
    refine' le_antisymm (smul_le r x) _
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_left (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert smul_le
    simp [h]
#align seminorm.of_smul_le Seminorm.ofSMulLE

def coeFnAddMonoidHom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add
#align seminorm.coe_fn_add_monoid_hom Seminorm.coeFnAddMonoidHom

def {p q : Seminorm 𝕜 E} : p ≤ q ↔ ∀ x, p x ≤ q x :=
  Iff.rfl
#align seminorm.le_def Seminorm.le_def

def {p q : Seminorm 𝕜 E} : p < q ↔ p ≤ q ∧ ∃ x, p x < q x :=
  @Pi.lt_def _ _ _ p q
#align seminorm.lt_def Seminorm.lt_def

def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
  { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Porting note: the `simp only` below used to be part of the `rw`.
    -- I'm not sure why this change was needed, and am worried by it!
    -- Note: #8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`

def pullback (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ →+ Seminorm 𝕜 E where
  toFun := fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f
#align seminorm.pullback Seminorm.pullback

def ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }
#align seminorm.ball Seminorm.ball

def closedBall (x : E) (r : ℝ) :=
  { y : E | p (y - x) ≤ r }
#align seminorm.closed_ball Seminorm.closedBall

def restrictScalars (p : Seminorm 𝕜' E) : Seminorm 𝕜 E :=
  { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }
#align seminorm.restrict_scalars Seminorm.restrictScalars

def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }
#align norm_seminorm normSeminorm

structure Seminorm (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  smul' : ∀ (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x
#align seminorm Seminorm