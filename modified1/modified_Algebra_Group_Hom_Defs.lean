def OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := map_one f

/-- Any type satisfying `OneHomClass` can be cast into `OneHom` via `OneHomClass.toOneHom`. -/
@[to_additive "Any type satisfying `ZeroHomClass` can be cast into `ZeroHom` via
`ZeroHomClass.toZeroHom`. "]
instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) :
    ((f : OneHom M N) : M → N) = f := rfl
#align one_hom.coe_coe OneHom.coe_coe

def MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M →ₙ* N where
  toFun := f
  map_mul' := map_mul f

/-- Any type satisfying `MulHomClass` can be cast into `MulHom` via `MulHomClass.toMulHom`. -/
@[to_additive "Any type satisfying `AddHomClass` can be cast into `AddHom` via
`AddHomClass.toAddHom`."]
instance [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]
theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M → N) = f := rfl
#align mul_hom.coe_coe MulHom.coe_coe

def MonoidHomClass.toMonoidHom [MonoidHomClass F M N] (f : F) : M →* N :=
  { (f : M →ₙ* N), (f : OneHom M N) with }

/-- Any type satisfying `MonoidHomClass` can be cast into `MonoidHom` via
`MonoidHomClass.toMonoidHom`. -/
@[to_additive "Any type satisfying `AddMonoidHomClass` can be cast into `AddMonoidHom` via
`AddMonoidHomClass.toAddMonoidHom`."]
instance [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]
theorem MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M →* N) : M → N) = f := rfl
#align monoid_hom.coe_coe MonoidHom.coe_coe

def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]
#align monoid_hom.mk' MonoidHom.mk'

def OneHom.copy [One M] [One N] (f : OneHom M N) (f' : M → N) (h : f' = f) :
    OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'
#align one_hom.copy OneHom.copy

def MulHom.copy [Mul M] [Mul N] (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    M →ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'
#align mul_hom.copy MulHom.copy

def MonoidHom.copy [MulOneClass M] [MulOneClass N] (f : M →* N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }
#align monoid_hom.copy MonoidHom.copy

def OneHom.id (M : Type*) [One M] : OneHom M M where
  toFun x := x
  map_one' := rfl
#align one_hom.id OneHom.id

def MulHom.id (M : Type*) [Mul M] : M →ₙ* M where
  toFun x := x
  map_mul' _ _ := rfl
#align mul_hom.id MulHom.id

def MonoidHom.id (M : Type*) [MulOneClass M] : M →* M where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.id MonoidHom.id

def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun := hnp ∘ hmn
  map_one' := by simp
#align one_hom.comp OneHom.comp

def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
  toFun := hnp ∘ hmn
  map_mul' x y := by simp
#align mul_hom.comp MulHom.comp

def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn
  map_one' := by simp
  map_mul' := by simp
#align monoid_hom.comp MonoidHom.comp

def End := M →* M
#align monoid.End Monoid.End

def End := A →+ A
#align add_monoid.End AddMonoid.End

structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 0 -/
  protected map_zero' : toFun 0 = 0
#align zero_hom ZeroHom

structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves addition -/
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
#align add_hom AddHom

structure AddMonoidHom (M : Type*) (N : Type*) [AddZeroClass M] [AddZeroClass N] extends
  ZeroHom M N, AddHom M N
#align add_monoid_hom AddMonoidHom

structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 1 -/
  protected map_one' : toFun 1 = 1
#align one_hom OneHom

structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves multiplication -/
  protected map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
#align mul_hom MulHom

structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N
#align monoid_hom MonoidHom