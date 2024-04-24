def {_ : CommSemiring R} [_s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) : algebraMap R (∀ i, f i) a = fun i => algebraMap R (f i) a :=
  rfl
#align pi.algebra_map_def Pi.algebraMap_def

def evalAlgHom {_ : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }
#align pi.eval_alg_hom Pi.evalAlgHom

def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }
#align pi.const_alg_hom Pi.constAlgHom

def compLeft (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }
#align alg_hom.comp_left AlgHom.compLeft

def piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R] [∀ i, Semiring (A₁ i)]
    [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }
#align alg_equiv.Pi_congr_right AlgEquiv.piCongrRight

structure on families of R-algebras

The R-algebra structure on `∀ i : I, A i` when each `A i` is an R-algebra.

## Main definitions

structure on `∀ i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.
variable {I} (R)

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
def evalAlgHom {_ : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }
#align pi.eval_alg_hom Pi.evalAlgHom