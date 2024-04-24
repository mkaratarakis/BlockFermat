def Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)
#align Hausdorffification Hausdorffification

def adicCompletion : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (h : m ≤ n), liftQ _ (mkQ _) (by
      rw [ker_mkQ]
      exact smul_mono (Ideal.pow_le_pow_right h) le_rfl)
    (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]
#align adic_completion adicCompletion

def of : M →ₗ[R] Hausdorffification I M :=
  mkQ _
#align Hausdorffification.of Hausdorffification.of

def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      exact smul_mono le_rfl le_top
#align Hausdorffification.lift Hausdorffification.lift

def of : M →ₗ[R] adicCompletion I M where
  toFun x := ⟨fun _ => mkQ _ x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.of adicCompletion.of

def eval (n : ℕ) : adicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.eval adicCompletion.eval