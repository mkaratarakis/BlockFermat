def Pi.mulHom {γ : Type w} [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y
#align pi.mul_hom Pi.mulHom

def Pi.monoidHom {γ : Type w} [∀ i, MulOneClass (f i)] [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }
#align pi.monoid_hom Pi.monoidHom

def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i
#align pi.eval_mul_hom Pi.evalMulHom

def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl
#align pi.const_mul_hom Pi.constMulHom

def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where
  toFun g := g
  map_mul' _ _ := rfl
#align mul_hom.coe_fn MulHom.coeFn

def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp
#align mul_hom.comp_left MulHom.compLeft

def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i
#align pi.eval_monoid_hom Pi.evalMonoidHom

def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl
#align pi.const_monoid_hom Pi.constMonoidHom

def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.coe_fn MonoidHom.coeFn

def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext; dsimp; simp
  map_mul' _ _ := by ext; simp
#align monoid_hom.comp_left MonoidHom.compLeft

def OneHom.single [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i
#align one_hom.single OneHom.single

def MonoidHom.single [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.single f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }
#align monoid_hom.single MonoidHom.single

def MulHom.single [∀ i, MulZeroClass <| f i] (i : I) : f i →ₙ* ∀ i, f i where
  toFun := Pi.single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _
#align mul_hom.single MulHom.single

def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1
#align function.extend_by_one.hom Function.ExtendByOne.hom