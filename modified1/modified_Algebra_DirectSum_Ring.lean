def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one := rfl

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom)

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
def gMulHom {i j} : A i →+ A j →+ A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _
#align direct_sum.gmul_hom DirectSum.gMulHom

def mulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gMulHom A
#align direct_sum.mul_hom DirectSum.mulHom

def ofZeroRingHom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }
#align direct_sum.of_zero_ring_hom DirectSum.ofZeroRingHom

def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
      refine DirectSum.addHom_ext' (fun yi ↦ AddMonoidHom.ext (fun yv ↦ ?_))
      show
        toAddMonoid f (of A xi xv * of A yi yv) =
          toAddMonoid f (of A xi xv) * toAddMonoid f (of A yi yv)
      simp_rw [of_mul_of, toAddMonoid_of]
      exact hmul _ _ }
#align direct_sum.to_semiring DirectSum.toSemiring

def liftRingHom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GOne.one = 1 ∧
          ∀ {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R) where
  toFun f := toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) →+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intros i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      rw [← F.map_mul (of A i ai), of_mul_of ai]⟩
  left_inv f := by
    ext xi xv
    exact toAddMonoid_of (fun _ => f.1) xi xv
  right_inv F := by
    apply RingHom.coe_addMonoidHom_injective
    refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
    simp only [RingHom.coe_addMonoidHom_mk, DirectSum.toAddMonoid_of, AddMonoidHom.mk_coe,
      AddMonoidHom.comp_apply, toSemiring_coe_addMonoidHom]
#align direct_sum.lift_ring_hom DirectSum.liftRingHom

structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `DirectSum.GNonUnitalNonAssocSemiring A`
* `DirectSum.GSemiring A`
* `DirectSum.GRing A`
* `DirectSum.GCommSemiring A`
* `DirectSum.GCommRing A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `DirectSum.nonUnitalNonAssocSemiring`, `DirectSum.nonUnitalNonAssocRing`
* `DirectSum.semiring`
* `DirectSum.ring`
* `DirectSum.commSemiring`
* `DirectSum.commRing`

the base ring `A 0` with:

* `DirectSum.GradeZero.nonUnitalNonAssocSemiring`,
  `DirectSum.GradeZero.nonUnitalNonAssocRing`
* `DirectSum.GradeZero.semiring`
* `DirectSum.GradeZero.ring`
* `DirectSum.GradeZero.commSemiring`
* `DirectSum.GradeZero.commRing`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `DirectSum.GradeZero.smul (A 0)`, `DirectSum.GradeZero.smulWithZero (A 0)`
* `DirectSum.GradeZero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`DirectSum.ofZeroRingHom : A 0 →+* ⨁ i, A i` provides `DirectSum.of A 0` as a ring
homomorphism.

`DirectSum.toSemiring` extends `DirectSum.toAddMonoid` to produce a `RingHom`.

## Direct sums of subobjects

structure derived from `GSemiring A`. -/
instance semiring : Semiring (⨁ i, A i) :=
  { (inferInstance : NonUnitalNonAssocSemiring _) with
    one := 1
    -- Porting note: not required in now
    -- mul := (· * ·)
    -- zero := 0
    -- add := (· + ·)
    one_mul := one_mul A
    mul_one := mul_one A
    mul_assoc := mul_assoc A
    natCast := fun n => of _ _ (GSemiring.natCast n)
    natCast_zero := by simp only [GSemiring.natCast_zero, map_zero]
    natCast_succ := fun n => by
      simp_rw [GSemiring.natCast_succ]
      rw [map_add]
      rfl }
#align direct_sum.semiring DirectSum.semiring

structure derived from `GCommSemiring A`. -/
instance commSemiring : CommSemiring (⨁ i, A i) :=
  { DirectSum.semiring A with
    mul_comm := mul_comm A }
#align direct_sum.comm_semiring DirectSum.commSemiring

structure to various
types of multiplicative structure.
-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

@[simp]
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl
#align direct_sum.of_zero_one DirectSum.of_zero_one

structure derived from `GSemiring A`. -/
instance GradeZero.semiring : Semiring (A 0) :=
  Function.Injective.semiring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ (of A 0).map_nsmul _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)
#align direct_sum.grade_zero.semiring DirectSum.GradeZero.semiring

structure from `GSemiring A`. Note that this results
in an overall `Module (A 0) (⨁ i, A i)` structure via `DirectSum.module`.
-/
instance GradeZero.module {i} : Module (A 0) (A i) :=
  letI := Module.compHom (⨁ i, A i) (ofZeroRingHom A)
  DFinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a
#align direct_sum.grade_zero.module DirectSum.GradeZero.module

structure derived from `GCommSemiring A`. -/
instance GradeZero.commSemiring : CommSemiring (A 0) :=
  Function.Injective.commSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of_zero_one A) (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)
#align direct_sum.grade_zero.comm_semiring DirectSum.GradeZero.commSemiring

structure originates from
`DirectSum.gsemiring.ofAddSubmonoids`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
      refine DirectSum.addHom_ext' (fun yi ↦ AddMonoidHom.ext (fun yv ↦ ?_))
      show
        toAddMonoid f (of A xi xv * of A yi yv) =
          toAddMonoid f (of A xi xv) * toAddMonoid f (of A yi yv)
      simp_rw [of_mul_of, toAddMonoid_of]
      exact hmul _ _ }
#align direct_sum.to_semiring DirectSum.toSemiring