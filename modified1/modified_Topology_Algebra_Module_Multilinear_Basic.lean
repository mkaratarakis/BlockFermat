def Simps.apply (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : ∀ i, M₁ i) : M₂ :=
  L₁ v
#align continuous_multilinear_map.simps.apply ContinuousMultilinearMap.Simps.apply

def applyAddHom (m : ∀ i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ →+ M₂ where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl
#align continuous_multilinear_map.apply_add_hom ContinuousMultilinearMap.applyAddHom

def toContinuousLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
  { f.toMultilinearMap.toLinearMap m i with
    cont := f.cont.comp (continuous_const.update i continuous_id) }
#align continuous_multilinear_map.to_continuous_linear_map ContinuousMultilinearMap.toContinuousLinearMap

def prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prod_mk g.cont }
#align continuous_multilinear_map.prod ContinuousMultilinearMap.prod

def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) :
    ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  cont := continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap
#align continuous_multilinear_map.pi ContinuousMultilinearMap.pi

def codRestrict (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    ContinuousMultilinearMap R M₁ p :=
  ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩
#align continuous_multilinear_map.cod_restrict ContinuousMultilinearMap.codRestrict

def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →L[R] M₃) ≃ ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
    (map_continuous f).comp <| continuous_pi fun _ ↦ continuous_id⟩
  left_inv _ := rfl
  right_inv f := toMultilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap
#align continuous_multilinear_map.of_subsingleton ContinuousMultilinearMap.ofSubsingleton

def constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const
#align continuous_multilinear_map.const_of_is_empty ContinuousMultilinearMap.constOfIsEmpty

def compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄ :=
  { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
    cont := g.cont.comp <| continuous_pi fun j => (f j).cont.comp <| continuous_apply _ }
#align continuous_multilinear_map.comp_continuous_linear_map ContinuousMultilinearMap.compContinuousLinearMap

def _root_.ContinuousLinearMap.compContinuousMultilinearMap (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }
#align continuous_linear_map.comp_continuous_multilinear_map ContinuousLinearMap.compContinuousMultilinearMap

def piEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] :
    (∀ i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  toFun := ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
#align continuous_multilinear_map.pi_equiv ContinuousMultilinearMap.piEquiv

def domDomCongr {ι' : Type*} (e : ι ≃ ι')
    (f : ContinuousMultilinearMap R (fun _ : ι => M₂) M₃) :
    ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toMultilinearMap := f.domDomCongr e
  cont := f.cont.comp <| continuous_pi fun _ => continuous_apply _
#align continuous_multilinear_map.dom_dom_congr ContinuousMultilinearMap.domDomCongr

def domDomCongrEquiv {ι' : Type*} (e : ι ≃ ι') :
    ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ ≃
      ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toFun := domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp
#align continuous_multilinear_map.dom_dom_congr_equiv ContinuousMultilinearMap.domDomCongrEquiv

def linearDeriv : (∀ i, M₁ i) →L[R] M₂ := ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]
lemma linearDeriv_apply : f.linearDeriv x y = ∑ i, f (Function.update x i (y i)) := by
  unfold linearDeriv toContinuousLinearMap
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Finset.sum_apply]
  rfl

end linearDeriv

/-- In the specific case of continuous multilinear maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `(i : Fin (n+1)) → M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) :=
  f.toMultilinearMap.cons_add m x y
#align continuous_multilinear_map.cons_add ContinuousMultilinearMap.cons_add

def restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  cont := f.cont
#align continuous_multilinear_map.restrict_scalars ContinuousMultilinearMap.restrictScalars

def toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ →ₗ[R'] MultilinearMap A M₁ M₂ where
  toFun := toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul
#align continuous_multilinear_map.to_multilinear_map_linear ContinuousMultilinearMap.toMultilinearMapLinear

def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R' (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R' (M' i)] [∀ i, ContinuousConstSMul R' (M' i)] :
    (∀ i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (∀ i, M' i) :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align continuous_multilinear_map.pi_linear_equiv ContinuousMultilinearMap.piLinearEquiv

def mkPiAlgebra : ContinuousMultilinearMap R (fun _ : ι => A) A where
  cont := continuous_finset_prod _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A
#align continuous_multilinear_map.mk_pi_algebra ContinuousMultilinearMap.mkPiAlgebra

def mkPiAlgebraFin : A[×n]→L[R] A where
  cont := by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A
#align continuous_multilinear_map.mk_pi_algebra_fin ContinuousMultilinearMap.mkPiAlgebraFin

def smulRight : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.smulRight z
  cont := f.cont.smul continuous_const
#align continuous_multilinear_map.smul_right ContinuousMultilinearMap.smulRight

def mkPiRing (z : M) : ContinuousMultilinearMap R (fun _ : ι => R) M :=
  (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z
#align continuous_multilinear_map.mk_pi_field ContinuousMultilinearMap.mkPiRing

structure ContinuousMultilinearMap (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] extends MultilinearMap R M₁ M₂ where
  cont : Continuous toFun
#align continuous_multilinear_map ContinuousMultilinearMap