def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f
#align linear_map.base_change LinearMap.baseChange

def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul
#align linear_map.base_change_hom LinearMap.baseChangeHom

def _root_.Module.End.baseChangeHom : Module.End R M →ₐ[R] Module.End A (A ⊗[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

lemma baseChange_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M →ₗ[R] N)

@[simp]
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  -- Porting note: `tmul_sub` wasn't needed in mathlib3
  simp [baseChange_eq_ltensor, tmul_sub]

#align linear_map.base_change_sub LinearMap.baseChange_sub

def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
#align algebra.tensor_product.one_def Algebra.TensorProduct.one_def

def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl

theorem natCast_def' (n : ℕ) : (n : A ⊗[R] B) = (1 : A) ⊗ₜ (n : B) := by
  rw [natCast_def, ← nsmul_one, smul_tmul, nsmul_one]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

#noalign algebra.tensor_product.mul_aux

def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)
#align algebra.tensor_product.mul Algebra.TensorProduct.mul

def includeLeftRingHom : A →+* A ⊗[R] B where
  toFun a := a ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [add_tmul]
  map_one' := rfl
  map_mul' := by simp
#align algebra.tensor_product.include_left_ring_hom Algebra.TensorProduct.includeLeftRingHom

def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=
  { includeLeftRingHom with commutes' := by simp }
#align algebra.tensor_product.include_left Algebra.TensorProduct.includeLeft

def includeRight : B →ₐ[R] A ⊗[R] B where
  toFun b := 1 ⊗ₜ b
  map_zero' := by simp
  map_add' := by simp [tmul_add]
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp only [algebraMap_apply']
#align algebra.tensor_product.include_right Algebra.TensorProduct.includeRight

def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

end NonUnitalNonAssocRing

section NonAssocRing
variable [CommRing R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonAssocRing : NonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

end NonAssocRing

section NonUnitalRing
variable [CommRing R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalRing : NonUnitalRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

end NonUnitalRing

section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

instance instCommSemiring : CommSemiring (A ⊗[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]

end CommSemiring

section Ring
variable [CommRing R]
variable [Ring A] [Algebra R A]
variable [Ring B] [Algebra R B]

instance instRing : Ring (A ⊗[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

theorem intCast_def' (z : ℤ) : (z : A ⊗[R] B) = (1 : A) ⊗ₜ (z : B) := by
  rw [intCast_def, ← zsmul_one, smul_tmul, zsmul_one]

-- verify there are no diamonds
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
-- fails at `with_reducible_and_instances rfl` #10906

def rightAlgebra : Algebra B (A ⊗[R] B) :=
  (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B).toAlgebra
#align algebra.tensor_product.right_algebra Algebra.TensorProduct.rightAlgebra

def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  AlgHom.ofLinearMap f h_one <| f.map_mul_iff.2 <| by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    exact h_mul _ _ _ _
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product Algebra.TensorProduct.algHomOfLinearMapTensorProduct

def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }
#align algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct

def algEquivOfLinearEquivTripleTensorProduct (f : (A ⊗[R] B) ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    exact h_mul _ _ _ _ _ _
#align algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct

def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun f g => LinearMap.ext fun x => rfl
          map_smul' := fun c g => LinearMap.ext fun x => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [f.map_mul, g.map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [f.map_one, g.map_one, one_mul])

@[simp]
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl

@[simp]
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun a b => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp

@[simp]
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp

@[simp]
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun x y =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])
#align algebra.tensor_product.lid Algebra.TensorProduct.lid

def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun _a₁ _a₂ _r₁ _r₂ => smul_mul_smul _ _ _ _ |>.symm)
    (one_smul _ _)
#align algebra.tensor_product.rid Algebra.TensorProduct.rid

def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl
#align algebra.tensor_product.comm Algebra.TensorProduct.comm

def assoc : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] B ⊗[R] C :=
  algEquivOfLinearEquivTripleTensorProduct
    (_root_.TensorProduct.assoc R A B C)
    Algebra.TensorProduct.assoc_aux_1
    Algebra.TensorProduct.assoc_aux_2
#align algebra.tensor_product.assoc Algebra.TensorProduct.assoc

def map (f : A →ₐ[S] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[S] B ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])
#align algebra.tensor_product.map Algebra.TensorProduct.map

def congr (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[S] B ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)
#align algebra.tensor_product.congr Algebra.TensorProduct.congr

def lmul' : S ⊗[R] S →ₐ[R] S :=
  algHomOfLinearMapTensorProduct (LinearMap.mul' R S)
    (fun a₁ a₂ b₁ b₂ => by simp only [LinearMap.mul'_apply, mul_mul_mul_comm]) <| by
    simp only [LinearMap.mul'_apply, _root_.mul_one]
#align algebra.tensor_product.lmul' Algebra.TensorProduct.lmul'

def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g
#align algebra.tensor_product.product_map Algebra.TensorProduct.productMap

def basisAux : A ⊗[R] M ≃ₗ[R] ι →₀ A :=
  _root_.TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique R A PUnit.{uι+1}).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))
#align algebra.tensor_product.basis_aux Algebra.TensorProduct.basisAux

def basis : Basis ι A (A ⊗[R] M) where
  repr := { basisAux A b with map_smul' := basisAux_map_smul b }
#align algebra.tensor_product.basis Algebra.TensorProduct.basis

def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)
#align module.End_tensor_End_alg_hom Module.endTensorEndAlgHom

def moduleAux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B →ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }
#align tensor_product.algebra.module_aux TensorProduct.Algebra.moduleAux

def module : Module (A ⊗[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting note: was one `simp only`, not two
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      -- Porting note: was one `simp only`, not two
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      -- Porting note: was one `simp only`, but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, LinearMap.map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw, smul_add]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [LinearMap.map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, LinearMap.map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]
#align tensor_product.algebra.module TensorProduct.Algebra.module

def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl
#align tensor_product.algebra.smul_def TensorProduct.Algebra.smul_def

structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.
- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

structure on `A ⊗[R] B`
-/

section AddCommMonoidWithOne

variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1

theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
#align algebra.tensor_product.one_def Algebra.TensorProduct.one_def

structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C]
variable [Semiring D] [Algebra R D]

/-- Build an algebra morphism from a linear map out of a tensor product, and evidence that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  AlgHom.ofLinearMap f h_one <| f.map_mul_iff.2 <| by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    exact h_mul _ _ _ _
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product Algebra.TensorProduct.algHomOfLinearMapTensorProduct