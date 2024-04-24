def comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a
#align has_smul.comp.smul SMul.comp.smul

def comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
#align has_smul.comp SMul.comp

def Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    MulAction M β where
  smul := (· • ·)
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]
#align function.injective.mul_action Function.Injective.mulAction

def Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    MulAction M β where
  smul := (· • ·)
  one_smul y := by
    rcases hf y with ⟨x, rfl⟩
    rw [← smul, one_smul]
  mul_smul c₁ c₂ y := by
    rcases hf y with ⟨x, rfl⟩
    simp only [← smul, mul_smul]
#align function.surjective.mul_action Function.Surjective.mulAction

def Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R M] [Monoid S]
    [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    MulAction S M where
  smul := (· • ·)
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
  mul_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_mul, hsmul, mul_smul]
#align function.surjective.mul_action_left Function.Surjective.mulActionLeft

def toFun : α ↪ M → α :=
  ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩
#align mul_action.to_fun MulAction.toFun

def compHom [Monoid N] (g : N →* M) :
    MulAction N α where
  smul := SMul.comp.smul g
  -- Porting note: was `by simp [g.map_one, MulAction.one_smul]`
  one_smul _ := by simpa [(· • ·)] using MulAction.one_smul ..
  -- Porting note: was `by simp [g.map_mul, MulAction.mul_smul]`
  mul_smul _ _ _ := by simpa [(· • ·)] using MulAction.mul_smul ..
#align mul_action.comp_hom MulAction.compHom

def
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f : E →* F) (a : E) (x : G) :
    letI : MulAction E G := MulAction.compHom _ f
    a • x = (f a) • x := rfl

/-- If an action is transitive, then composing this action with a surjective homomorphism gives
again a transitive action. -/
@[to_additive]
theorem isPretransitive_compHom
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] [IsPretransitive F G]
    {f : E →* F} (hf : Surjective f) :
    letI : MulAction E G := MulAction.compHom _ f
    IsPretransitive E G := by
  let _ : MulAction E G := MulAction.compHom _ f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : F, m • x = y := exists_smul_eq F x y
  obtain ⟨e, rfl⟩ : ∃ e, f e = m := hf m
  exact ⟨e, rfl⟩

@[to_additive]
theorem IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α]
    [IsPretransitive M α] (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) :
    IsPretransitive N α :=
  ⟨fun x y ↦ (exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩⟩

@[to_additive]
theorem IsPretransitive.of_compHom
    {M N α : Type*} [Monoid M] [Monoid N] [MulAction N α]
    (f : M →* N) [h : letI := compHom α f; IsPretransitive M α] :
    IsPretransitive N α :=
  letI := compHom α f; h.of_smul_eq f rfl

end MulAction

end

section CompatibleScalar

@[to_additive]
theorem smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]
#align smul_one_smul smul_one_smul

def MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]
#align smul_one_hom MonoidHom.smulOneHom

def monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] :
    (M →* N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where
  toFun f := ⟨MulAction.compHom N f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ MonoidHom.smulOneHom
  left_inv f := MonoidHom.ext fun m ↦ mul_one (f m)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| MulAction.ext _ _ <| funext₂ <| smul_one_smul N

end CompatibleScalar

/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
#align smul_zero_class SMulZeroClass

def Function.Injective.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul := (· • ·)
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]
#align function.injective.smul_zero_class Function.Injective.smulZeroClass

def ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  -- Porting note: `simp` no longer works here.
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]
#align zero_hom.smul_zero_class ZeroHom.smulZeroClass

def Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroClass R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    SMulZeroClass S M where
  smul := (· • ·)
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]
#align function.surjective.smul_zero_class_left Function.Surjective.smulZeroClassLeft

def SMulZeroClass.compFun (f : N → M) :
    SMulZeroClass N A where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)
#align smul_zero_class.comp_fun SMulZeroClass.compFun

def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x
#align smul_zero_class.to_zero_hom SMulZeroClass.toZeroHom

def Function.Injective.distribSMul [AddZeroClass B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.smulZeroClass f.toZeroHom smul with
    smul_add := fun c x y => hf <| by simp only [smul, map_add, smul_add] }
#align function.injective.distrib_smul Function.Injective.distribSMul

def Function.Surjective.distribSMul [AddZeroClass B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }
#align function.surjective.distrib_smul Function.Surjective.distribSMul

def Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }
#align function.surjective.distrib_smul_left Function.Surjective.distribSMulLeft

def DistribSMul.compFun (f : N → M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }
#align distrib_smul.comp_fun DistribSMul.compFun

def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (· • ·) x, map_add' := smul_add x }
#align distrib_smul.to_add_monoid_hom DistribSMul.toAddMonoidHom

def Function.Injective.distribMulAction [AddMonoid B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }
#align function.injective.distrib_mul_action Function.Injective.distribMulAction

def Function.Surjective.distribMulAction [AddMonoid B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }
#align function.surjective.distrib_mul_action Function.Surjective.distribMulAction

def Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }
#align function.surjective.distrib_mul_action_left Function.Surjective.distribMulActionLeft

def DistribMulAction.compHom [Monoid N] (f : N →* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with }
#align distrib_mul_action.comp_hom DistribMulAction.compHom

def DistribMulAction.toAddMonoidHom (x : M) : A →+ A :=
  DistribSMul.toAddMonoidHom A x
#align distrib_mul_action.to_add_monoid_hom DistribMulAction.toAddMonoidHom

def DistribMulAction.toAddMonoidEnd :
    M →* AddMonoid.End A where
  toFun := DistribMulAction.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' x y := AddMonoidHom.ext <| mul_smul x y
#align distrib_mul_action.to_add_monoid_End DistribMulAction.toAddMonoidEnd

def Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul_mul := fun c x y => hf <| by simp only [smul, f.map_mul, smul_mul'],
    smul_one := fun c => hf <| by simp only [smul, f.map_one, smul_one] }
#align function.injective.mul_distrib_mul_action Function.Injective.mulDistribMulAction

def Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul_mul := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_mul', ← smul, ← f.map_mul],
    smul_one := fun c => by rw [← f.map_one, ← smul, smul_one] }
#align function.surjective.mul_distrib_mul_action Function.Surjective.mulDistribMulAction

def MulDistribMulAction.compHom [Monoid N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }
#align mul_distrib_mul_action.comp_hom MulDistribMulAction.compHom

def MulDistribMulAction.toMonoidHom (r : M) :
    A →* A where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r
#align mul_distrib_mul_action.to_monoid_hom MulDistribMulAction.toMonoidHom

def MulDistribMulAction.toMonoidEnd :
    M →* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y
#align mul_distrib_mul_action.to_monoid_End MulDistribMulAction.toMonoidEnd

def Function.End :=
  α → α
#align function.End Function.End

def (f : Function.End α) (a : α) : f • a = f a :=
  rfl
#align function.End.smul_def Function.End.smul_def

def (f g : Function.End α) : (f * g) = f ∘ g :=
  rfl

--TODO - This statement should be somethting like `toFun 1 = id`
theorem Function.End.one_def : (1 : Function.End α) = id :=
  rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α :=
  ⟨fun {_ _} => funext⟩
#align function.End.apply_has_faithful_smul Function.End.apply_FaithfulSMul

def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl
#align add_monoid.End.smul_def AddMonoid.End.smul_def

def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
#align mul_action.to_End_hom MulAction.toEndHom

def MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f
#align mul_action.of_End_hom MulAction.ofEndHom

def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom
#align add_action.to_End_hom AddAction.toEndHom

def AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f
#align add_action.of_End_hom AddAction.ofEndHom

structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `SMulCommClass S R` on the appropriate modules. When
the caller has `CommSemiring R`, they can set `S = R` and `smulCommClass_self` will populate the
instance. If the caller only has `Semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`AddCommMonoid.nat_smulCommClass` or `AddCommMonoid.nat_smulCommClass'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `LinearMap.prod_equiv`.
-/


/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive]
theorem SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α :=
  ⟨fun a' a b => (smul_comm a a' b).symm⟩
#align smul_comm_class.symm SMulCommClass.symm