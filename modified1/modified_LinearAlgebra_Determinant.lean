def equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
    (e : (m → R) ≃ₗ[R] n → R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)
#align equiv_of_pi_lequiv_pi equivOfPiLEquivPi

def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n :=
  equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)
#align matrix.index_equiv_of_inv Matrix.indexEquivOfInv

def detAux : Trunc (Basis ι A M) → (M →ₗ[A] M) →* A :=
  Trunc.lift
    (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M →ₗ[A] M) →* Matrix ι ι A))
    fun b c => MonoidHom.ext <| det_toMatrix_eq_det_toMatrix b c
#align linear_map.det_aux LinearMap.detAux

def LinearMap.detAux_def'

theorem detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
    (b' : Basis ι' A M) (f : M →ₗ[A] M) :
    LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']
#align linear_map.det_aux_def' LinearMap.detAux_def''

def det : (M →ₗ[A] M) →* A :=
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.choose_spec.some)
  else 1
#align linear_map.det LinearMap.det

def det : (M ≃ₗ[R] M) →* Rˣ :=
  (Units.map (LinearMap.det : (M →ₗ[R] M) →* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom
#align linear_equiv.det LinearEquiv.det

def LinearEquiv.ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc
      toLin v' v (toMatrix v v' f)⁻¹ (f x) = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x :=
        by rw [toLin_mul v v' v, toLin_toMatrix, LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc
      f (toLin v' v (toMatrix v v' f)⁻¹ x) =
          toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x :=
        by rw [toLin_mul v' v v', LinearMap.comp_apply, toLin_toMatrix v v']
      _ = x := by simp [h]
#align linear_equiv.of_is_unit_det LinearEquiv.ofIsUnitDet

def LinearMap.equivOfDetNeZero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (f : M →ₗ[𝕜] M) (hf : LinearMap.det f ≠ 0) : M ≃ₗ[𝕜] M :=
  have : IsUnit (LinearMap.toMatrix (FiniteDimensional.finBasis 𝕜 M)
      (FiniteDimensional.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this
#align linear_map.equiv_of_det_ne_zero LinearMap.equivOfDetNeZero

def Basis.det : M [⋀^ι]→ₗ[R] R where
  toFun v := det (e.toMatrix v)
  map_add' := by
    intro inst v i x y
    cases Subsingleton.elim inst ‹_›
    simp only [e.toMatrix_update, LinearEquiv.map_add, Finsupp.coe_add]
    -- Porting note: was `exact det_update_column_add _ _ _ _`
    convert det_updateColumn_add (e.toMatrix v) i (e.repr x) (e.repr y)
  map_smul' := by
    intro inst u i c x
    cases Subsingleton.elim inst ‹_›
    simp only [e.toMatrix_update, Algebra.id.smul_eq_mul, LinearEquiv.map_smul]
    -- Porting note: was `apply det_update_column_smul`
    convert det_updateColumn_smul (e.toMatrix u) i c (e.repr x)
  map_eq_zero_of_eq' := by
    intro v i j h hij
    -- Porting note: added
    simp only
    rw [← Function.update_eq_self i v, h, ← det_transpose, e.toMatrix_update, ← updateRow_transpose,
      ← e.toMatrix_transpose_apply]
    apply det_zero_of_row_eq hij
    rw [updateRow_ne hij.symm, updateRow_self]
#align basis.det Basis.det

def
    have : ⇑v' = v := by
      ext i
      rw [v'_def, Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩
#align is_basis_iff_det is_basis_iff_det