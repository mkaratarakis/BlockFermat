def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { Pi.addHom fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }
#align linear_map.pi LinearMap.pi

def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.proj LinearMap.proj

def compLeft (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }
#align linear_map.comp_left LinearMap.compLeft

def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] (i : ι) → φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }
#align linear_map.single LinearMap.single

def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : ((i : ι) → φ i →ₗ[R] M) ≃ₗ[S] ((i : ι) → φ i) →ₗ[R] M where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  right_inv f := by
    ext x
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]
#align linear_map.lsum LinearMap.lsum

def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) ≃ₗ[R] (i : I) → φ i := by
  refine'
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _
  · intro b
    simp only [mem_iInf, mem_ker, funext_iff, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_codRestrict, proj_pi, Subtype.coe_prop]
    ext b ⟨j, hj⟩
    simp only [dif_pos, Function.comp_apply, Function.eval_apply, LinearMap.codRestrict_apply,
      LinearMap.coe_comp, LinearMap.coe_proj, LinearMap.pi_apply, Submodule.subtype_apply,
      Subtype.coe_prop]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_iInf, mem_ker, proj_apply] using (mem_iInf _).1 hb
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, codRestrict_apply]
    split_ifs with h
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm
#align linear_map.infi_ker_proj_equiv LinearMap.iInfKerProjEquiv

def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j
#align linear_map.diag LinearMap.diag

def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
  carrier := Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)
#align submodule.pi Submodule.pi

def piCongrRight (e : (i : ι) → φ i ≃ₗ[R] ψ i) : ((i : ι) → φ i) ≃ₗ[R] (i : ι) → ψ i :=
  { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }
#align linear_equiv.Pi_congr_right LinearEquiv.piCongrRight

def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗ[R] (i : ι') → φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.Pi_congr_left' LinearEquiv.piCongrLeft'

def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗ[R] (i : ι) → φ i :=
  (piCongrLeft' R φ e.symm).symm
#align linear_equiv.Pi_congr_left LinearEquiv.piCongrLeft

def piOptionEquivProd {ι : Type*} {M : Option ι → Type*} [(i : Option ι) → AddCommGroup (M i)]
    [(i : Option ι) → Module R (M i)] :
    ((i : Option ι) → M i) ≃ₗ[R] M none × ((i : ι) → M (some i)) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [Function.funext_iff]
    map_smul' := by simp [Function.funext_iff] }
#align linear_equiv.pi_option_equiv_prod LinearEquiv.piOptionEquivProd

def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)
#align linear_equiv.pi_ring LinearEquiv.piRing

def sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (Sum α β → M) ≃ₗ[R] (α → M) × (β → M) :=
  { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }
#align linear_equiv.sum_arrow_lequiv_prod_arrow LinearEquiv.sumArrowLequivProdArrow

def funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M :=
  { Equiv.funUnique ι M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.fun_unique LinearEquiv.funUnique

def piFinTwo (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    ((i : Fin 2) → M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align linear_equiv.pi_fin_two LinearEquiv.piFinTwo

def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }
#align linear_equiv.fin_two_arrow LinearEquiv.finTwoArrow

def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }
#align function.extend_by_zero.linear_map Function.ExtendByZero.linearMap

def LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃ where
  toFun _ := Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
#align linear_map.vec_empty LinearMap.vecEmpty

def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂ where
  toFun m := Matrix.vecCons (f m) (g m)
  map_add' x y := by
    simp only []
    rw [f.map_add, g.map_add, Matrix.cons_add_cons (f x)]
  map_smul' c x := by
    simp only []
    rw [f.map_smul, g.map_smul, RingHom.id_apply, Matrix.smul_cons c (f x)]
#align linear_map.vec_cons LinearMap.vecCons

def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Fin 0 → M₃ where
  toFun _ := LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
#align linear_map.vec_empty₂ LinearMap.vecEmpty₂

def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Fin n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Fin n.succ → M₃ where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]
#align linear_map.vec_cons₂ LinearMap.vecCons₂