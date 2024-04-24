def toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ :=
  { e with }
#align affine_equiv.to_affine_map AffineEquiv.toAffineMap

def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃ[k] P₂ where
  toFun := e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv p' := by simp [h p', vadd_vsub, vsub_vadd]
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), vadd_vsub, vsub_vadd]
  linear := e'
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), vadd_vsub_assoc, vadd_vadd]
#align affine_equiv.mk' AffineEquiv.mk'

def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
  toEquiv := e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
    e.toEquiv.symm.apply_eq_iff_eq_symm_apply.2 <| by
      rw [Equiv.symm_symm, e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v),
        LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
#align affine_equiv.symm AffineEquiv.symm

def Simps.apply (e : P₁ ≃ᵃ[k] P₂) : P₁ → P₂ :=
  e
#align affine_equiv.simps.apply AffineEquiv.Simps.apply

def Simps.symm_apply (e : P₁ ≃ᵃ[k] P₂) : P₂ → P₁ :=
  e.symm
#align affine_equiv.simps.symm_apply AffineEquiv.Simps.symm_apply

def ofBijective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective φ) : P₁ ≃ᵃ[k] P₂ :=
  { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }
#align affine_equiv.of_bijective AffineEquiv.ofBijective

def refl : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl
#align affine_equiv.refl AffineEquiv.refl

def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
  toEquiv := e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    simp only [LinearEquiv.trans_apply, coe_toEquiv, (· ∘ ·), Equiv.coe_trans, map_vadd]
#align affine_equiv.trans AffineEquiv.trans

def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ :=
  rfl
#align affine_equiv.one_def AffineEquiv.one_def

def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e :=
  rfl
#align affine_equiv.mul_def AffineEquiv.mul_def

def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
  rfl
#align affine_equiv.inv_def AffineEquiv.inv_def

def linearHom : (P₁ ≃ᵃ[k] P₁) →* V₁ ≃ₗ[k] V₁ where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl
#align affine_equiv.linear_hom AffineEquiv.linearHom

def equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ →ᵃ[k] P₁)ˣ where
  toFun e :=
    { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ →ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ →ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := AffineMap.congr_fun u.mul_inv
      linear :=
        LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ <| Units.map AffineMap.linearHom u
      map_vadd' := fun _ _ => (u : P₁ →ᵃ[k] P₁).map_vadd _ _ }
  left_inv _ := AffineEquiv.ext fun _ => rfl
  right_inv _ := Units.ext <| AffineMap.ext fun _ => rfl
  map_mul' _ _ := rfl
#align affine_equiv.equiv_units_affine_map AffineEquiv.equivUnitsAffineMap

def vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _
#align affine_equiv.vadd_const AffineEquiv.vaddConst

def constVSub (p : P₁) : P₁ ≃ᵃ[k] V₁ where
  toEquiv := Equiv.constVSub p
  linear := LinearEquiv.neg k
  map_vadd' p' v := by simp [vsub_vadd_eq_vsub_sub, neg_add_eq_sub]
#align affine_equiv.const_vsub AffineEquiv.constVSub

def constVAdd (v : V₁) : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _
#align affine_equiv.const_vadd AffineEquiv.constVAdd

def constVAddHom : Multiplicative V₁ →* P₁ ≃ᵃ[k] P₁ where
  toFun v := constVAdd k P₁ (Multiplicative.toAdd v)
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁
#align affine_equiv.const_vadd_hom AffineEquiv.constVAddHom

def homothetyUnitsMulHom (p : P) : Rˣ →* P ≃ᵃ[R] P :=
  equivUnitsAffineMap.symm.toMonoidHom.comp <| Units.map (AffineMap.homothetyHom p)
#align affine_equiv.homothety_units_mul_hom AffineEquiv.homothetyUnitsMulHom

def pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)
#align affine_equiv.point_reflection AffineEquiv.pointReflection

def toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where
  toEquiv := e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p
#align linear_equiv.to_affine_equiv LinearEquiv.toAffineEquiv

structure with multiplication corresponding to
composition in `AffineEquiv.group`.

## Tags

structure AffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p
#align affine_equiv AffineEquiv