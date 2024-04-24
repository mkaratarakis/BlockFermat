def Function.Injective.smulWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]
#align function.injective.smul_with_zero Function.Injective.smulWithZero

def Function.Surjective.smulWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]
#align function.surjective.smul_with_zero Function.Surjective.smulWithZero

def SMulWithZero.compHom (f : ZeroHom R' R) : SMulWithZero R' M where
  smul := (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by show (f 0) • m = 0; rw [map_zero, zero_smul]
#align smul_with_zero.comp_hom SMulWithZero.compHom

def Function.Injective.mulActionWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZero

def Function.Surjective.mulActionWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZero

def MulActionWithZero.compHom (f : R' →*₀ R) : MulActionWithZero R' M :=
  { SMulWithZero.compHom M f.toZeroHom with
    mul_smul := fun r s m => by show f (r * s) • m = (f r) • (f s) • m; simp [mul_smul]
    one_smul := fun m => by show (f 1) • m = m; simp }
#align mul_action_with_zero.comp_hom MulActionWithZero.compHom

def smulMonoidWithZeroHom {α β : Type*} [MonoidWithZero α] [MulZeroOneClass β]
    [MulActionWithZero α β] [IsScalarTower α β β] [SMulCommClass α β β] : α × β →*₀ β :=
  { smulMonoidHom with map_zero' := smul_zero _ }
#align smul_monoid_with_zero_hom smulMonoidWithZeroHom

structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.smulWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]
#align function.injective.smul_with_zero Function.Injective.smulWithZero

structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.smulWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]
#align function.surjective.smul_with_zero Function.Surjective.smulWithZero

structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulActionWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZero

structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulActionWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZero