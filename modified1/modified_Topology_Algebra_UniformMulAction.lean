def (c : M) (x : Completion X) : c • x = Completion.map (c • ·) x :=
  rfl
#align uniform_space.completion.smul_def UniformSpace.Completion.smul_def

def UniformSpace.Completion.vadd_def

@[to_additive]
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun _ => uniformContinuous_map⟩

@[to_additive instVAddAssocClass]
instance instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : Completion X → Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine' Eq.trans _ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩
#align uniform_space.completion.is_scalar_tower UniformSpace.Completion.instIsScalarTower

structure is set up, we provide
* `UniformSpace.Completion.DistribMulAction`
* `UniformSpace.Completion.MulActionWithZero`
* `UniformSpace.Completion.Module`

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/


universe u v w x y

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

/-- An additive action such that for all `c`, the map `fun x ↦ c +ᵥ x` is uniformly continuous. -/
class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous (c +ᵥ · : X → X)
#align has_uniform_continuous_const_vadd UniformContinuousConstVAdd