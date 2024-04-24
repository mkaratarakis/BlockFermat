def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i :=
  DFinsupp.lmk
#align direct_sum.lmk DirectSum.lmk

def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i :=
  DFinsupp.lsingle
#align direct_sum.lof DirectSum.lof

def toModule : (⨁ i, M i) →ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum ℕ) φ
#align direct_sum.to_module DirectSum.toModule

def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i ↦ lof R T (fun i : Subtype T ↦ M i) ⟨i, H i.prop⟩
#align direct_sum.lset_to_set DirectSum.lsetToSet

def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  { DFinsupp.equivFunOnFintype with
    toFun := (↑)
    map_add' := fun f g ↦ by
      ext
      rw [add_apply, Pi.add_apply]
    map_smul' := fun c f ↦ by
      simp_rw [RingHom.id_apply]
      rw [DFinsupp.coe_smul] }
#align direct_sum.linear_equiv_fun_on_fintype DirectSum.linearEquivFunOnFintype

def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ ↦ LinearMap.id with }
#align direct_sum.lid DirectSum.lid

def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  DFinsupp.lapply i
#align direct_sum.component DirectSum.component

def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  { equivCongrLeft h with map_smul' := DFinsupp.comapDomain'_smul h.invFun h.right_inv }
#align direct_sum.lequiv_congr_left DirectSum.lequivCongrLeft

def sigmaLcurry : (⨁ i : Σi, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r ↦ by convert DFinsupp.sigmaCurry_smul (δ := δ) r }
#align direct_sum.sigma_lcurry DirectSum.sigmaLcurry

def sigmaLuncurry [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σ_, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }
#align direct_sum.sigma_luncurry DirectSum.sigmaLuncurry

def sigmaLcurryEquiv [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ i : Σ_, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurryEquiv, sigmaLcurry R with }
#align direct_sum.sigma_lcurry_equiv DirectSum.sigmaLcurryEquiv

def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }
#align direct_sum.lequiv_prod_direct_sum DirectSum.lequivProdDirectSum

def coeLinearMap : (⨁ i, A i) →ₗ[R] M :=
  toModule R ι M fun i ↦ (A i).subtype
#align direct_sum.coe_linear_map DirectSum.coeLinearMap

def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σi, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm
#align direct_sum.is_internal.collected_basis DirectSum.IsInternal.collectedBasis