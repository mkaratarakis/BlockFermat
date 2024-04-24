def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl
#align ulift.smul_def ULift.smul_def

def ULift.vadd_def

instance isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩
#align ulift.is_scalar_tower ULift.isScalarTower

def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift.{w} M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift
#align ulift.module_equiv ULift.moduleEquiv