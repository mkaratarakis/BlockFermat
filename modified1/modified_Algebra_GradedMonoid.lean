def GradedMonoid (A : ι → Type*) :=
  Sigma A
#align graded_monoid GradedMonoid

def mk {A : ι → Type*} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk
#align graded_monoid.mk GradedMonoid.mk

def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, _ => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GMul.mul (gnpowRec _ a) a)
#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.GMonoid.gnpowRec

def mkZeroMonoidHom : A 0 →* GradedMonoid A where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHom

def List.dProdIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0
#align list.dprod_index List.dProdIndex

def List.dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x
#align list.dprod List.dProd

def SetLike.Homogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i
#align set_like.is_homogeneous SetLike.Homogeneous

def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.Homogeneous A a }
  one_mem' := SetLike.homogeneous_one A
  mul_mem' a b := SetLike.homogeneous_mul a b
#align set_like.homogeneous_submonoid SetLike.homogeneousSubmonoid

structure
over the sigma type `GradedMonoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `GradedMonoid.GOne A`
* `GradedMonoid.GMul A`
* `GradedMonoid.GMonoid A`
* `GradedMonoid.GCommMonoid A`

These respectively imbue:

* `One (GradedMonoid A)`
* `Mul (GradedMonoid A)`
* `Monoid (GradedMonoid A)`
* `CommMonoid (GradedMonoid A)`

the base type `A 0` with:

* `GradedMonoid.GradeZero.One`
* `GradedMonoid.GradeZero.Mul`
* `GradedMonoid.GradeZero.Monoid`
* `GradedMonoid.GradeZero.CommMonoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `GradedMonoid.GradeZero.SMul (A 0)`
* `GradedMonoid.GradeZero.MulAction (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `DirectSum.Ring` and the rest
of that file.

## Dependent graded products

structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type*)

section One

variable [Zero ι] [GOne A]

/-- `1 : A 0` is the value provided in `GOne.one`. -/
@[nolint unusedArguments]
instance GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩
#align graded_monoid.grade_zero.has_one GradedMonoid.GradeZero.one

structure derived from `GMonoid A`. -/
instance GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoid

structure derived from `GCommMonoid A`. -/
instance GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoid

structure from `GMonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul
#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulAction