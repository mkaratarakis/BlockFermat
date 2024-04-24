def one [One β] : One α :=
  ⟨e.symm 1⟩
#align equiv.has_one Equiv.one

def [One β] :
    letI := e.one
    1 = e.symm 1 :=
  rfl
#align equiv.one_def Equiv.one_def

def Equiv.zero_def

@[to_additive]
noncomputable instance [Small.{v} α] [One α] : One (Shrink.{v} α) :=
  (equivShrink α).symm.one

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Add` across an `Equiv`"]
protected def mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩
#align equiv.has_mul Equiv.mul

def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) :=
  rfl
#align equiv.mul_def Equiv.mul_def

def Equiv.add_def

@[to_additive]
noncomputable instance [Small.{v} α] [Mul α] : Mul (Shrink.{v} α) :=
  (equivShrink α).symm.mul

/-- Transfer `Div` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Sub` across an `Equiv`"]
protected def div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩
#align equiv.has_div Equiv.div

def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) :=
  rfl
#align equiv.div_def Equiv.div_def

def Equiv.sub_def

@[to_additive]
noncomputable instance [Small.{v} α] [Div α] : Div (Shrink.{v} α) :=
  (equivShrink α).symm.div

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Neg` across an `Equiv`"]
protected def Inv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩
#align equiv.has_inv Equiv.Inv

def [Inv β] (x : α) :
    letI := Equiv.Inv e
    x⁻¹ = e.symm (e x)⁻¹ :=
  rfl
#align equiv.inv_def Equiv.inv_def

def Equiv.neg_def

@[to_additive]
noncomputable instance [Small.{v} α] [Inv α] : Inv (Shrink.{v} α) :=
  (equivShrink α).symm.Inv

/-- Transfer `SMul` across an `Equiv` -/
@[reducible]
protected def smul (R : Type*) [SMul R β] : SMul R α :=
  ⟨fun r x => e.symm (r • e x)⟩
#align equiv.has_smul Equiv.smul

def {R : Type*} [SMul R β] (r : R) (x : α) :
    letI := e.smul R
    r • x = e.symm (r • e x) :=
  rfl
#align equiv.smul_def Equiv.smul_def

def pow (N : Type*) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩
#align equiv.has_pow Equiv.pow

def {N : Type*} [Pow β N] (n : N) (x : α) :
    letI := e.pow N
    x ^ n = e.symm (e x ^ n) :=
  rfl
#align equiv.pow_def Equiv.pow_def

def mulEquiv (e : α ≃ β) [Mul β] :
    let mul := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.mul_equiv Equiv.mulEquiv

def _root_.Shrink.mulEquiv [Small.{v} α] [Mul α] : Shrink.{v} α ≃* α :=
  (equivShrink α).symm.mulEquiv

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp [add_def]
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.ring_equiv Equiv.ringEquiv

def _root_.Shrink.ringEquiv [Small.{v} α] [Ring α] : Shrink.{v} α ≃+* α :=
  (equivShrink α).symm.ringEquiv

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `add_semigroup` across an `Equiv`"]
protected def semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _
#align equiv.semigroup Equiv.semigroup

def semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup_with_zero Equiv.semigroupWithZero

def commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _
#align equiv.comm_semigroup Equiv.commSemigroup

def mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_class Equiv.mulZeroClass

def mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_one_class Equiv.mulOneClass

def mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_one_class Equiv.mulZeroOneClass

def monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.monoid Equiv.monoid

def commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_monoid Equiv.commMonoid

def group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.group Equiv.group

def commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_group Equiv.commGroup

def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_semiring Equiv.nonUnitalNonAssocSemiring

def nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_semiring Equiv.nonUnitalSemiring

def addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.symm n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }
#align equiv.add_monoid_with_one Equiv.addMonoidWithOne

def addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun n =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }
#align equiv.add_group_with_one Equiv.addGroupWithOne

def nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_semiring Equiv.nonAssocSemiring

def semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semiring Equiv.semiring

def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_semiring Equiv.nonUnitalCommSemiring

def commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semiring Equiv.commSemiring

def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_ring Equiv.nonUnitalNonAssocRing

def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_ring Equiv.nonUnitalRing

def nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_ring Equiv.nonAssocRing

def ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.ring Equiv.ring

def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_ring Equiv.nonUnitalCommRing

def commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_ring Equiv.commRing

def RatCast [RatCast β] : RatCast α where ratCast n := e.symm n
#align equiv.has_rat_cast Equiv.RatCast

def divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let rat_cast := e.RatCast
  let qsmul := e.smul ℚ
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.division_ring Equiv.divisionRing

def field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let rat_cast := e.RatCast
  let qsmul := e.smul ℚ
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.field Equiv.field

def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.smul R with
    one_smul := by simp [smul_def]
    mul_smul := by simp [smul_def, mul_smul] }
#align equiv.mul_action Equiv.mulAction

def distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α := by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)
#align equiv.distrib_mul_action Equiv.distribMulAction

def module (e : α ≃ β) [AddCommMonoid β] :
    let addCommMonoid := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α := by
  intros
  exact
    ({ Equiv.distribMulAction R e with
        zero_smul := by simp [smul_def, zero_smul, zero_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)
#align equiv.module Equiv.module

def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] : by
    let addCommMonoid := Equiv.addCommMonoid e
    let module := Equiv.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
        exact Iff.mpr (apply_eq_iff_eq_symm_apply _) rfl }
#align equiv.linear_equiv Equiv.linearEquiv

def _root_.Shrink.linearEquiv [Small.{v} α] [AddCommMonoid α] [Module R α] :
    Shrink.{v} α ≃ₗ[R] α :=
  Equiv.linearEquiv _ (equivShrink α).symm

end

section

variable [CommSemiring R]

/-- Transfer `Algebra` across an `Equiv` -/
@[reducible]
protected def algebra (e : α ≃ β) [Semiring β] :
    let semiring := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := by
  intros
  letI : Module R α := e.module R
  fapply Algebra.ofModule
  · intro r x y
    show e.symm (e (e.symm (r • e x)) * e y) = e.symm (r • e.ringEquiv (x * y))
    simp only [apply_symm_apply, Algebra.smul_mul_assoc, map_mul, ringEquiv_apply]
  · intro r x y
    show e.symm (e x * e (e.symm (r • e y))) = e.symm (r • e (e.symm (e x * e y)))
    simp only [apply_symm_apply, Algebra.mul_smul_comm]
#align equiv.algebra Equiv.algebra

def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    (algebraMap R α) r = e.symm ((algebraMap R β) r) := by
  intros
  simp only [Algebra.algebraMap_eq_smul_one]
  show e.symm (r • e 1) = e.symm (r • 1)
  simp only [Equiv.one_def, apply_symm_apply]

noncomputable instance [Small.{v} α] [Semiring α] [Algebra R α] :
    Algebra R (Shrink.{v} α) :=
  (equivShrink α).symm.algebra _

/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }
#align equiv.alg_equiv Equiv.algEquiv

structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

### Implementation details

structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive "An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] :
    let mul := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.mul_equiv Equiv.mulEquiv

structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp [add_def]
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.ring_equiv Equiv.ringEquiv

structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] : by
    let addCommMonoid := Equiv.addCommMonoid e
    let module := Equiv.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
        exact Iff.mpr (apply_eq_iff_eq_symm_apply _) rfl }
#align equiv.linear_equiv Equiv.linearEquiv

structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }
#align equiv.alg_equiv Equiv.algEquiv