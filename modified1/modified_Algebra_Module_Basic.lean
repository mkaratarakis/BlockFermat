def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n :=
  rfl
#align add_monoid.End.nat_cast_def AddMonoid.End.nat_cast_def

def Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ →+ M)
    (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
    add_smul := fun c₁ c₂ x => hf <| by simp only [smul, f.map_add, add_smul]
    zero_smul := fun x => hf <| by simp only [smul, zero_smul, f.map_zero] }
#align function.injective.module Function.Injective.module

def Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M →+ M₂)
    (hf : Surjective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero, ← smul, zero_smul] }
#align function.surjective.module Function.Surjective.module

def Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [SMul S M] (f : R →+* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }
#align function.surjective.module_left Function.Surjective.moduleLeft

def Module.compHom [Semiring S] (f : S →+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S →* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication

def Module.toAddMonoidEnd : R →+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    -- Porting note: the two `show`s weren't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication

def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom
#align smul_add_hom smulAddHom

def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z :=
  rfl
#align add_monoid.End.int_cast_def AddMonoid.End.int_cast_def

def Module.addCommMonoidToAddCommGroup [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M :=
  { (inferInstance : AddCommMonoid M) with
    neg := fun a => (-1 : R) • a
    add_left_neg := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 2 [← one_smul R a]
        rw [← add_smul, add_left_neg, zero_smul]
    zsmul := fun z a => (z : R) • a
    zsmul_zero' := fun a => by simpa only [Int.cast_zero] using zero_smul R a
    zsmul_succ' := fun z a => by simp [add_comm, add_smul]
    zsmul_neg' := fun z a => by simp [← smul_assoc, neg_one_smul] }
#align module.add_comm_monoid_to_add_comm_group Module.addCommMonoidToAddCommGroup

def RingHom.toModule [Semiring R] [Semiring S] (f : R →+* S) : Module R S :=
  Module.compHom S f
#align ring_hom.to_module RingHom.toModule

def RingHom.smulOneHom
    [Semiring R] [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] : R →+* S where
  __ := MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)

/-- A homomorphism between semirings R and S can be equivalently specified by a R-module
structure on S such that S/S/R is a scalar tower. -/
def ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] :
    (R →+* S) ≃ {_inst : Module R S // IsScalarTower R S S} where
  toFun f := ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ RingHom.smulOneHom
  left_inv f := RingHom.ext fun r ↦ mul_one (f r)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| Module.ext _ _ <| funext₂ <| smul_one_smul S

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
theorem nsmul_eq_smul_cast (n : ℕ) (b : M) : n • b = (n : R) • b := by
  induction' n with n ih
  · rw [Nat.zero_eq, Nat.cast_zero, zero_smul, zero_smul]
  · rw [Nat.succ_eq_add_one, Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]
#align nsmul_eq_smul_cast nsmul_eq_smul_cast

def AddCommMonoid.natModule.unique : Unique (Module ℕ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert nat_smul_eq_nsmul P n
#align add_comm_monoid.nat_module.unique AddCommMonoid.natModule.unique

def AddCommGroup.intModule.unique : Unique (Module ℤ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n
#align add_comm_group.int_module.unique AddCommGroup.intModule.unique

structure along an injective additive monoid homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ →+ M)
    (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
    add_smul := fun c₁ c₂ x => hf <| by simp only [smul, f.map_add, add_smul]
    zero_smul := fun x => hf <| by simp only [smul, zero_smul, f.map_zero] }
#align function.injective.module Function.Injective.module

structure along a surjective additive monoid homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M →+ M₂)
    (hf : Surjective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero, ← smul, zero_smul] }
#align function.surjective.module Function.Surjective.module

structure by `r • x = f r * x`. -/
def RingHom.toModule [Semiring R] [Semiring S] (f : R →+* S) : Module R S :=
  Module.compHom S f
#align ring_hom.to_module RingHom.toModule

structure on S such that S/S/R is a scalar tower. -/
def ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] :
    (R →+* S) ≃ {_inst : Module R S // IsScalarTower R S S} where
  toFun f := ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ RingHom.smulOneHom
  left_inv f := RingHom.ext fun r ↦ mul_one (f r)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| Module.ext _ _ <| funext₂ <| smul_one_smul S

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
theorem nsmul_eq_smul_cast (n : ℕ) (b : M) : n • b = (n : R) • b := by
  induction' n with n ih
  · rw [Nat.zero_eq, Nat.cast_zero, zero_smul, zero_smul]
  · rw [Nat.succ_eq_add_one, Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]
#align nsmul_eq_smul_cast nsmul_eq_smul_cast

structure by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) :
    @SMul.smul ℕ M h.toSMul n x = n • x := by rw [nsmul_eq_smul_cast ℕ n x, Nat.cast_id]; rfl
#align nat_smul_eq_nsmul nat_smul_eq_nsmul

structure by design. -/
def AddCommMonoid.natModule.unique : Unique (Module ℕ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert nat_smul_eq_nsmul P n
#align add_comm_monoid.nat_module.unique AddCommMonoid.natModule.unique

structure via a cast. -/
theorem zsmul_eq_smul_cast (n : ℤ) (b : M) : n • b = (n : R) • b :=
  have : (smulAddHom ℤ M).flip b = ((smulAddHom R M).flip b).comp (Int.castAddHom R) := by
    apply AddMonoidHom.ext_int
    simp
  DFunLike.congr_fun this n
#align zsmul_eq_smul_cast zsmul_eq_smul_cast

structure by design. -/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) :
    @SMul.smul ℤ M h.toSMul n x = n • x := by rw [zsmul_eq_smul_cast ℤ n x, Int.cast_id]; rfl
#align int_smul_eq_zsmul int_smul_eq_zsmul

structure by design. -/
def AddCommGroup.intModule.unique : Unique (Module ℤ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n
#align add_comm_group.int_module.unique AddCommGroup.intModule.unique

structure on an additive commutative group. -/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩
#align subsingleton_rat_module subsingleton_rat_module