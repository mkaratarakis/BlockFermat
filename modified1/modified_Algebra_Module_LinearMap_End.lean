def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl
#align linear_map.smul_def LinearMap.smul_def

def toLinearMap (s : S) : M →ₗ[R] M where
  toFun := HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _
#align distrib_mul_action.to_linear_map DistribMulAction.toLinearMap

def toModuleEnd : S →* Module.End R M where
  toFun := toLinearMap R M
  map_one' := LinearMap.ext <| one_smul _
  map_mul' _ _ := LinearMap.ext <| mul_smul _ _
#align distrib_mul_action.to_module_End DistribMulAction.toModuleEnd

def toModuleEnd : S →+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with
    toFun := DistribMulAction.toLinearMap R M
    map_zero' := LinearMap.ext <| zero_smul S
    map_add' := fun _ _ ↦ LinearMap.ext <| add_smul _ _ }
#align module.to_module_End Module.toModuleEnd

def moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with
    toFun := DistribMulAction.toLinearMap R R
    invFun := fun f ↦ MulOpposite.op (f 1)
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring <| one_mul _ }
#align module.module_End_self Module.moduleEndSelf

def moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with
    toFun := DistribMulAction.toLinearMap _ _
    invFun := fun f ↦ f 1
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring_op <| mul_one _ }
#align module.module_End_self_op Module.moduleEndSelfOp

def (n : ℕ) [AddCommMonoid N₁] [Module R N₁] :
    (↑n : Module.End R N₁) = Module.toModuleEnd R N₁ n :=
  rfl
#align module.End.nat_cast_def Module.End.natCast_def

def (z : ℤ) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z :=
  rfl
#align module.End.int_cast_def Module.End.intCast_def

def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by dsimp only; rw [f.map_add, add_smul]
  map_smul' b y := by dsimp; rw [map_smul, smul_assoc]
#align linear_map.smul_right LinearMap.smulRight

def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _
#align linear_map.applyₗ' LinearMap.applyₗ'

def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃ where
  toFun := f.comp
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul f _ _
#align linear_map.comp_right LinearMap.compRight

def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }
#align linear_map.applyₗ LinearMap.applyₗ

def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul
#align linear_map.smul_rightₗ LinearMap.smulRightₗ

structure above with composition as multiplication.

-/

universe u v

/-- Linear endomorphisms of a module, with associated ring structure
`Module.End.semiring` and algebra structure `Module.End.algebra`. -/
abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M
#align module.End Module.End

structure of endomorphisms
-/

section Endomorphisms

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

instance : One (Module.End R M) := ⟨LinearMap.id⟩

instance : Mul (Module.End R M) := ⟨LinearMap.comp⟩

theorem one_eq_id : (1 : Module.End R M) = id := rfl
#align linear_map.one_eq_id LinearMap.one_eq_id