def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }
#align matrix.special_linear_group Matrix.SpecialLinearGroup

def transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R :=
  ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

-- Porting note: shouldn't be `@[simp]` because cast+mk gets reduced anyway
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl
#align matrix.special_linear_group.coe_mk Matrix.SpecialLinearGroup.coe_mk

def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R where
  toFun A :=
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_right_inv, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, mul_left_inv, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul ↑ₘA ↑ₘB
#align matrix.special_linear_group.to_lin' Matrix.SpecialLinearGroup.toLin'

def toGL : SpecialLinearGroup n R →* GeneralLinearGroup R (n → R) :=
  (GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp toLin'
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.to_GL Matrix.SpecialLinearGroup.toGL

def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S where
  toFun g :=
    ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul ↑ₘx ↑ₘy
#align matrix.special_linear_group.map Matrix.SpecialLinearGroup.map

def center_equiv_rootsOfUnity' (i : n) :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n).toPNat' R where
  toFun A := rootsOfUnity.mkOfPowEq (↑ₘA i i) <| by
    have : Nonempty n := ⟨i⟩
    obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
    replace hr' : A.val i i = r := by simp [← hr']
    simp [hr, hr']
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
    Subgroup.mem_center_iff.mpr fun B ↦ Subtype.val_injective <| by simp [coe_mul]⟩
  left_inv A := by
    refine SetCoe.ext <| SetCoe.ext ?_
    obtain ⟨r, _, hr⟩ := mem_center_iff.mp A.property
    simpa [← hr, Submonoid.smul_def, Units.smul_def] using smul_one_eq_diagonal r
  right_inv a := by
    obtain ⟨⟨a, _⟩, ha⟩ := a
    exact SetCoe.ext <| Units.eq_iff.mp <| by simp
  map_mul' A B := by
    dsimp
    ext
    simp only [Submonoid.coe_mul, coe_mul, rootsOfUnity.val_mkOfPowEq_coe, Units.val_mul]
    rw [← scalar_eq_coe_self_center A i, ← scalar_eq_coe_self_center B i]
    simp

open scoped Classical in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity.

See also `center_equiv_rootsOfUnity'`. -/
noncomputable def center_equiv_rootsOfUnity :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n).toPNat' R :=
  (isEmpty_or_nonempty n).by_cases
  (fun hn ↦ by
    rw [center_eq_bot_of_subsingleton, Fintype.card_eq_zero, Nat.toPNat'_zero, rootsOfUnity_one]
    exact MulEquiv.mulEquivOfUnique)
  (fun hn ↦ center_equiv_rootsOfUnity' (Classical.arbitrary n))

end center

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g
#align matrix.special_linear_group.coe_matrix_coe Matrix.SpecialLinearGroup.coe_matrix_coe

def S : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩
#align modular_group.S ModularGroup.S

def T : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩
#align modular_group.T ModularGroup.T

structure on `SpecialLinearGroup n R` and the embedding into the general linear group
`GeneralLinearGroup R (n → R)`.

## Main definitions

structure (under multiplication)
 * `Matrix.SpecialLinearGroup.toGL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

structure for all `CommRing R`.

We define the elements of `SpecialLinearGroup` to be matrices, since we need to
compute their determinant. This is in contrast with `GeneralLinearGroup R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `Matrix.SpecialLinearGroup.hasCoeToFun` for convenience, but do not state any
lemmas about it, and use `Matrix.SpecialLinearGroup.coeFn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References