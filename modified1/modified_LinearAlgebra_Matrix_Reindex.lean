def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A :=
  { reindex eₘ eₙ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align matrix.reindex_linear_equiv Matrix.reindexLinearEquiv

def reindexAlgEquiv (e : m ≃ n) : Matrix m m R ≃ₐ[R] Matrix n n R :=
  { reindexLinearEquiv R R e e with
    toFun := reindex e e
    map_mul' := fun a b => (reindexLinearEquiv_mul R R e e e a b).symm
    -- Porting note: `submatrix_smul` needed help
    commutes' := fun r => by simp [algebraMap, Algebra.toRingHom, submatrix_smul _ 1] }
#align matrix.reindex_alg_equiv Matrix.reindexAlgEquiv