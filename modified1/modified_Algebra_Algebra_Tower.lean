def lsmul : A →ₐ[R] Module.End B M where
  toFun := DistribMulAction.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r
#align algebra.lsmul Algebra.lsmulₓ

def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
#align is_scalar_tower.algebra.ext IsScalarTower.Algebra.ext

def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := fun _ => (algebraMap_apply _ _ _ _).symm }
#align is_scalar_tower.to_alg_hom IsScalarTower.toAlgHom

def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_hom.restrict_scalars AlgHom.restrictScalars

def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_equiv.restrict_scalars AlgEquiv.restrictScalars