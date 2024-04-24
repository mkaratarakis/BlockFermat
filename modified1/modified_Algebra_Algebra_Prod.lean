def r a, Algebra.smul_def r b] }
#align prod.algebra Prod.algebra

def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun _r => rfl }
#align alg_hom.fst AlgHom.fst

def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun _r => rfl }
#align alg_hom.snd AlgHom.snd

def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }
#align alg_hom.prod AlgHom.prod

def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C)
    where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align alg_hom.prod_equiv AlgHom.prodEquiv

structure on products of R-algebras

The R-algebra structure on `(i : I) → A i` when each `A i` is an R-algebra.

## Main definitions