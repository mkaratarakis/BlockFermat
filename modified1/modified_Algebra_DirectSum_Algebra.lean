def : ∀ (r) (x : GradedMonoid A), r • x = .mk _ (toFun r) * x
#align direct_sum.galgebra DirectSum.GAlgebra

def r ⟨i, xi⟩)

theorem algebraMap_apply (r : R) :
    algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (GAlgebra.toFun r) :=
  rfl
#align direct_sum.algebra_map_apply DirectSum.algebraMap_apply

def toAlgebra (f : ∀ i, A i →ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      show toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, one_def,
        ← lof_eq_of R, toModule_lof, hone] }
#align direct_sum.to_algebra DirectSum.toAlgebra

def gMulLHom {i j} : A i →ₗ[R] A j →ₗ[R] A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_smul' := fun r x => by
        injection (smul_comm r (GradedMonoid.mk _ a) (GradedMonoid.mk _ x)).symm
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_smul' r x := LinearMap.ext fun y => by
    injection smul_assoc r (GradedMonoid.mk _ x) (GradedMonoid.mk _ y)
  map_add' _ _ := LinearMap.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

end DirectSum

/-! ### Concrete instances -/

def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
#align algebra.direct_sum_galgebra Algebra.directSumGAlgebra

structure of a semiring. In this file, we introduce the `DirectSum.GAlgebra R A` class for the case
where all `A i` are `R`-modules. This is the extra structure needed to promote `⨁ i, A i` to an
`R`-algebra.

## Main definitions

structure originates from
`DirectSum.GMonoid.ofAddSubmodules`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
def toAlgebra (f : ∀ i, A i →ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => by
      show toModule R _ _ f (algebraMap R _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, one_def,
        ← lof_eq_of R, toModule_lof, hone] }
#align direct_sum.to_algebra DirectSum.toAlgebra