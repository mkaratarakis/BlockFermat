def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop :=
  B x y = 0
#align linear_map.is_ortho LinearMap.IsOrtho

def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
#align linear_map.is_ortho_def LinearMap.isOrtho_def

def IsOrthoᵢ (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) (v : n → M₁) : Prop :=
  Pairwise (B.IsOrtho on v)
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho LinearMap.IsOrthoᵢ

def {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {v : n → M₁} :
    B.IsOrthoᵢ v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho_def LinearMap.isOrthoᵢ_def

def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0
#align linear_map.is_refl LinearMap.IsRefl

def IsSymm (B : M →ₛₗ[I] M →ₗ[R] R) : Prop :=
  ∀ x y, I (B x y) = B y x
#align linear_map.is_symm LinearMap.IsSymm

def IsAlt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x, B x x = 0
#align linear_map.is_alt LinearMap.IsAlt

def orthogonalBilin (N : Submodule R₁ M₁) (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Submodule R₁ M₁
    where
  carrier := { m | ∀ n ∈ N, B.IsOrtho n m }
  zero_mem' x _ := B.isOrtho_zero_right x
  add_mem' hx hy n hn := by
    rw [LinearMap.IsOrtho, map_add, show B n _ = 0 from hx n hn, show B n _ = 0 from hy n hn,
      zero_add]
  smul_mem' c x hx n hn := by
    rw [LinearMap.IsOrtho, LinearMap.map_smulₛₗ, show B n x = 0 from hx n hn, smul_zero]
#align submodule.orthogonal_bilin Submodule.orthogonalBilin

def IsAdjointPair :=
  ∀ x y, B' (f x) y = B x (g y)
#align linear_map.is_adjoint_pair LinearMap.IsAdjointPair

def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
#align linear_map.is_pair_self_adjoint LinearMap.IsPairSelfAdjoint

def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
#align linear_map.is_self_adjoint LinearMap.IsSelfAdjoint

def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
#align linear_map.is_pair_self_adjoint_submodule LinearMap.isPairSelfAdjointSubmodule

def IsSkewAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f (-f)
#align linear_map.is_skew_adjoint LinearMap.IsSkewAdjoint

def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B
#align linear_map.self_adjoint_submodule LinearMap.selfAdjointSubmodule

def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B) B
#align linear_map.skew_adjoint_submodule LinearMap.skewAdjointSubmodule

def SeparatingLeft (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ x : M₁, (∀ y : M₂, B x y = 0) → x = 0
#align linear_map.separating_left LinearMap.SeparatingLeft

def SeparatingRight (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0
#align linear_map.separating_right LinearMap.SeparatingRight

def Nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  SeparatingLeft B ∧ SeparatingRight B
#align linear_map.nondegenerate LinearMap.Nondegenerate