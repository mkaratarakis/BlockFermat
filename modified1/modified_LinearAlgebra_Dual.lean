def Dual :=
  M →ₗ[R] R
#align module.dual Module.Dual

def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id
#align module.dual_pairing Module.dualPairing

def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id
#align module.dual.eval Module.Dual.eval

def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip
#align module.dual.transpose Module.Dual.transpose

def need to specify some parameters to transpose explicitly
theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose (R := R) u l = l.comp u :=
  rfl
#align module.dual.transpose_apply Module.Dual.transpose_apply

def need to specify some parameters to transpose explicitly
theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (R := R) (u.comp v) = (transpose (R := R) v).comp (transpose (R := R) u) :=
  rfl
#align module.dual.transpose_comp Module.Dual.transpose_comp

def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R
#align module.dual_prod_dual_equiv_dual Module.dualProdDualEquivDual

def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
-- Porting note: with reducible def need to specify some parameters to transpose explicitly
  Module.Dual.transpose (R := R) f
#align linear_map.dual_map LinearMap.dualMap

def need to specify some parameters to transpose explicitly
theorem LinearMap.dualMap_def (f : M₁ →ₗ[R] M₂) : f.dualMap = Module.Dual.transpose (R := R) f :=
  rfl
#align linear_map.dual_map_def LinearMap.dualMap_def

def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where
  __ := f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.left_inv x)
#align linear_equiv.dual_map LinearEquiv.dualMap

def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0
#align basis.to_dual Basis.toDual

def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m
#align basis.to_dual_flip Basis.toDualFlip

def toDualEquiv : M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective b.toDual ⟨ker_eq_bot.mp b.toDual_ker, range_eq_top.mp b.toDual_range⟩
#align basis.to_dual_equiv Basis.toDualEquiv

def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv
#align basis.dual_basis Basis.dualBasis

def evalEquiv : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ (bijective_dual_eval R M)
#align module.eval_equiv Module.evalEquiv

def mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M)) :=
  Submodule.orderIsoMapComap (evalEquiv R M)
#align module.map_eval_equiv Module.mapEvalEquiv

def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic| intros; apply Set.toFinite))

elab "use_finite_instance" : tactic => evalUseFiniteInstance

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed

def coeffs [DecidableEq ι] (h : DualBases e ε) (m : M) : ι →₀ R where
  toFun i := ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
#align module.dual_bases.coeffs Module.DualBases.coeffs

def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.sum fun (i : ι) (a : R) => a • e i
#align module.dual_bases.lc Module.DualBases.lc

def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.total _ _ R e l :=
  rfl
#align module.dual_bases.lc_def Module.DualBases.lc_def

def basis : Basis ι R M :=
  Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }
#align module.dual_bases.basis Module.DualBases.basis

def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W
#align submodule.dual_restrict Submodule.dualRestrict

def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl
#align submodule.dual_restrict_def Submodule.dualRestrict_def

def dualAnnihilator {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
-- Porting note (#11036): broken dot notation lean4#1910 LinearMap.ker

def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)
#align submodule.dual_coannihilator Submodule.dualCoannihilator

def dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V → Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl
#align subspace.dual_annihilator_gci Subspace.dualAnnihilatorGci

def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  (Classical.choose <| W.subtype.exists_leftInverse_of_injective W.ker_subtype).dualMap
#align subspace.dual_lift Subspace.dualLift

def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective
#align subspace.quot_annihilator_equiv Subspace.quotAnnihilatorEquiv

def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective
#align subspace.dual_equiv_dual Subspace.dualEquivDual

def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl
#align subspace.dual_equiv_dual_def Subspace.dualEquivDual_def

def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
  LinearEquiv.quotEquivOfQuotEquiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual
#align subspace.quot_dual_equiv_annihilator Subspace.quotDualEquivAnnihilator

def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator
  -- Porting note: this prevents the timeout; ML3 proof preserved below
  -- refine' _ ≪≫ₗ W.quotDualEquivAnnihilator
  -- refine' LinearEquiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv
  -- exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual
#align subspace.quot_equiv_annihilator Subspace.quotEquivAnnihilator

def dualCopairing (W : Submodule R M) : W.dualAnnihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
  LinearMap.flip <|
    W.liftQ ((Module.dualPairing R M).domRestrict W.dualAnnihilator).flip
      (by
        intro w hw
        ext ⟨φ, hφ⟩
        exact (mem_dualAnnihilator φ).mp hφ w hw)
#align submodule.dual_copairing Submodule.dualCopairing

def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator →ₗ[R] W →ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl
#align submodule.dual_pairing Submodule.dualPairing

def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinear
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
-- Porting note (#11036): broken dot notation lean4#1910 LinearMap.mem_range_self

def quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) :
    M ⧸ W.dualCoannihilator →ₗ[R] Dual R W :=
  liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]
theorem quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w : W) :
    W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m := rfl

theorem quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual :=
  LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

theorem flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual.flip :=
  fun _ _ he ↦ Subtype.ext <| LinearMap.ext fun m ↦ DFunLike.congr_fun he ⟦m⟧

open LinearMap in
theorem quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) :
    W.quotDualCoannihilatorToDual.Nondegenerate := by
  rw [Nondegenerate, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot]
  letI : AddCommGroup W := inferInstance
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

end Submodule

namespace LinearMap

open Submodule

-- Porting note (#11036): broken dot notation lean4#1910 LinearMap.range

def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm
#align subspace.dual_quot_distrib Subspace.dualQuotDistrib

def orderIsoFiniteCodimDim :
    {W : Subspace K V // FiniteDimensional K (V ⧸ W)} ≃o
    {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where
  toFun W := toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype.ext dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open OrderDual in
/-- For any finite-dimensional vector space, `dualAnnihilator` and `dualCoannihilator` give
  an antitone order isomorphism between the subspaces in the vector space and the subspaces
  in its dual. -/
def orderIsoFiniteDimensional [FiniteDimensional K V] :
    Subspace K V ≃o (Subspace K (Dual K V))ᵒᵈ where
  toFun W := toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open Submodule in
theorem dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] :
    W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V) := by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  haveI := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  haveI := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw [FiniteDimensional.eq_of_le_of_finrank_eq (map_le_dualAnnihilator_dualAnnihilator W)]
  rw [← (equivMapOfInjective _ (eval_apply_injective K (V := V)) W).finrank_eq, e1.finrank_eq]
  exact e2.finrank_eq

theorem map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] :
    W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator := by
  rw [← dualAnnihilator_dualAnnihilator_eq_map, dualCoannihilator_dualAnnihilator_eq]

end Subspace

end FiniteDimensional

end VectorSpace

namespace TensorProduct

variable (R A : Type*) (M : Type*) (N : Type*)
variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

open BigOperators

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight ↑(TensorProduct.lid R R) ∘ₗ homTensorHomMap R M N R R
#align tensor_product.dual_distrib TensorProduct.dualDistrib

def dualDistrib : Dual A M ⊗[R] Dual R N →ₗ[A] Dual A (M ⊗[R] N) :=
  compRight (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R A M N (f ⊗ₜ g) (m ⊗ₜ n) = g n • f m :=
  rfl

end AlgebraTensorModule

variable {R M N}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- An inverse to `TensorProduct.dualDistrib` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  -- Porting note: ∑ (i) (j) does not seem to work; applyₗ needs a little help to unify
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      (applyₗ (R := R) (c j)) ∘ₗ (applyₗ (R := R) (b i)) ∘ₗ lcurry R M N R
#align tensor_product.dual_distrib_inv_of_basis TensorProduct.dualDistribInvOfBasis

def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine' LinearEquiv.ofLinear (dualDistrib R M N) (dualDistribInvOfBasis b c) _ _
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _
#align tensor_product.dual_distrib_equiv_of_basis TensorProduct.dualDistribEquivOfBasis

def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)
#align tensor_product.dual_distrib_equiv TensorProduct.dualDistribEquiv

structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) : Prop where
  eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0
  protected total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  protected finite : ∀ m : M, { i | ε i m ≠ 0 }.Finite := by
      use_finite_instance
#align module.dual_bases Module.DualBases