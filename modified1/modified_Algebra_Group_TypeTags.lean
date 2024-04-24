def Additive (α : Type*) := α
#align additive Additive

def Multiplicative (α : Type*) := α
#align multiplicative Multiplicative

def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align additive.of_mul Additive.ofMul

def toMul : Additive α ≃ α := ofMul.symm
#align additive.to_mul Additive.toMul

def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align multiplicative.of_add Multiplicative.ofAdd

def toAdd : Multiplicative α ≃ α := ofAdd.symm
#align multiplicative.to_add Multiplicative.toAdd

def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative AddMonoidHom.toMultiplicative

def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => toMul (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align monoid_hom.to_additive MonoidHom.toAdditive

def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative' AddMonoidHom.toMultiplicative'

def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm
#align monoid_hom.to_additive' MonoidHom.toAdditive'

def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => toMul (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative'' AddMonoidHom.toMultiplicative''

def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm
#align monoid_hom.to_additive'' MonoidHom.toAdditive''

structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β (toMul a) :=
  ⟨fun a => CoeFun.coe (toMul a)⟩
#align additive.has_coe_to_fun Additive.coeToFun

structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β (toAdd a) :=
  ⟨fun a => CoeFun.coe (toAdd a)⟩
#align multiplicative.has_coe_to_fun Multiplicative.coeToFun