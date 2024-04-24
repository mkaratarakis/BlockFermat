def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0
#align ring_hom.is_integral_elem RingHom.IsIntegralElem

def RingHom.IsIntegral (f : R →+* A) :=
  ∀ x : A, f.IsIntegralElem x
#align ring_hom.is_integral RingHom.IsIntegral

def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x
#align is_integral IsIntegral

def Algebra.IsIntegral : Prop :=
  ∀ x : A, IsIntegral R x
#align algebra.is_integral Algebra.IsIntegral

def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap
#align integral_closure integralClosure

def AlgHom.mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.restrictDomain (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
theorem AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/-- An `AlgEquiv` between two rings restrict to an `AlgEquiv` between the integral closures inside
them. -/
def AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S :=
  AlgEquiv.ofAlgHom (f : A →ₐ[R] S).mapIntegralClosure (f.symm : S →ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ ↦ Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ ↦ Subtype.ext (f.left_inv _))

@[simp]
theorem AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.eq <| by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩
#align integral_closure.is_integral integralClosure.isIntegral

def normalizeScaleRoots (p : R[X]) : R[X] :=
  ∑ i in p.support,
    monomial i (if i = p.natDegree then 1 else p.coeff i * p.leadingCoeff ^ (p.natDegree - 1 - i))
#align normalize_scale_roots normalizeScaleRoots

def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)
#align is_integral_closure.mk' IsIntegralClosure.mk'

def lift : S →ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap (h x))
  map_one' := by simp only [RingHom.map_one, mk'_one]
  map_zero' := by simp only [RingHom.map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, RingHom.map_add]
  map_mul' x y := by simp_rw [← mk'_mul, RingHom.map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]
#align is_integral_closure.lift IsIntegralClosure.lift

def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom (lift _ B (isIntegral_algebra R B)) (lift _ B (isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)
#align is_integral_closure.equiv IsIntegralClosure.equiv