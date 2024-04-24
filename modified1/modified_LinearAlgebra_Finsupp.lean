def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv_fun_on_finite Finsupp.linearEquivFunOnFinite

def LinearEquiv.finsuppUnique : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv.finsupp_unique Finsupp.LinearEquiv.finsuppUnique

def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }
#align finsupp.lsingle Finsupp.lsingle

def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }
#align finsupp.lapply Finsupp.lapply

def lcoeFun : (α →₀ M) →ₗ[R] α → M where
  toFun := (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
#align finsupp.lcoe_fun Finsupp.lcoeFun

def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M
    where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl
#align finsupp.lsubtype_domain Finsupp.lsubtypeDomain

def supported (s : Set α) : Submodule R (α →₀ M) where
  carrier := { p | ↑p.support ⊆ s }
  add_mem' {p q} hp hq := by
    classical
    refine' Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) _) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_setOf_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  smul_mem' a p hp := Subset.trans (Finset.coe_subset.2 support_smul) hp
#align finsupp.supported Finsupp.supported

def restrictDom (s : Set α) [DecidablePred (· ∈ s)] : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· ∈ s) l
#align finsupp.restrict_dom Finsupp.restrictDom

def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s →₀ M := by
  let F : supported M R s ≃ (s →₀ M) := restrictSupportEquiv s M
  refine' F.toLinearEquiv _
  have :
    (F : supported M R s → ↥s →₀ M) =
      (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _
#align finsupp.supported_equiv_finsupp Finsupp.supportedEquivFinsupp

def lsum : (α → M →ₗ[R] N) ≃ₗ[S] (α →₀ M) →ₗ[R] N where
  toFun F :=
    { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
    ext x y
    simp
  map_add' F G := by
    ext x y
    simp
  map_smul' F G := by
    ext x y
    simp
#align finsupp.lsum Finsupp.lsum

def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R ℕ M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[ℕ] _).toAddEquiv
#align finsupp.lift Finsupp.lift

def llift : (X → M) ≃ₗ[S] (X →₀ R) →ₗ[R] M :=
  { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }
#align finsupp.llift Finsupp.llift

def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M
    where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul
#align finsupp.lmap_domain Finsupp.lmapDomain

def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M
    where
  toFun l := Finsupp.comapDomain f l (hf.injOn _)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
#align finsupp.lcomap_domain Finsupp.lcomapDomain

def total : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)
#align finsupp.total Finsupp.total

def totalOn (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((Finsupp.total _ _ _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_total _).2 ⟨l, hl, rfl⟩
#align finsupp.total_on Finsupp.totalOn

def domLCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv <| by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using (lmapDomain M R e).map_smul
#align finsupp.dom_lcongr Finsupp.domLCongr

def congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t := by
  haveI := Classical.decPred fun x => x ∈ s
  haveI := Classical.decPred fun x => x ∈ t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)
#align finsupp.congr Finsupp.congr

def mapRange.linearMap (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] α →₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    -- Porting note: `hf` should be specified.
    map_smul' := fun c v => mapRange_smul (hf := f.map_zero) c v (f.map_smul c) }
#align finsupp.map_range.linear_map Finsupp.mapRange.linearMap

def mapRange.linearEquiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }
#align finsupp.map_range.linear_equiv Finsupp.mapRange.linearEquiv

def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (ι →₀ M) ≃ₗ[R] κ →₀ N :=
  (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)
#align finsupp.lcongr Finsupp.lcongr

def sumFinsuppLEquivProdFinsupp {α β : Type*} : (Sum α β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        -- Porting note: `add_equiv.to_fun_eq_coe` →
        --               `Equiv.toFun_as_coe` & `AddEquiv.toEquiv_eq_coe` & `AddEquiv.coe_toEquiv`
        simp only [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Prod.smul_fst,
          Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }
#align finsupp.sum_finsupp_lequiv_prod_finsupp Finsupp.sumFinsuppLEquivProdFinsupp

def sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] : ((Σ j, ιs j) →₀ M) ≃ₗ[R] (j : _) → (ιs j →₀ M) :=
  -- Porting note: `ιs` should be specified.
  { sigmaFinsuppAddEquivPiFinsupp (ιs := ιs) with
    map_smul' := fun c f => by
      ext
      simp }
#align finsupp.sigma_finsupp_lequiv_pi_finsupp Finsupp.sigmaFinsuppLEquivPiFinsupp

def finsuppProdLEquiv {α β : Type*} (R : Type*) {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M :=
  { finsuppProdEquiv with
    map_add' := fun f g => by
      ext
      simp [finsuppProdEquiv, curry_apply]
    map_smul' := fun c f => by
      ext
      simp [finsuppProdEquiv, curry_apply] }
#align finsupp.finsupp_prod_lequiv Finsupp.finsuppProdLEquiv

def Fintype.total : (α → M) →ₗ[S] (α → R) →ₗ[R] M where
  toFun v :=
    { toFun := fun f => ∑ i, f i • v i
      map_add' := fun f g => by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
      map_smul' := fun r f => by simp_rw [Finset.smul_sum, smul_smul]; rfl }
  map_add' u v := by ext; simp [Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Finset.smul_sum, smul_comm]
#align fintype.total Fintype.total

def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_total _ _ _).mp x.2).choose
#align span.repr Span.repr

def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m := by
    letI := Module.subsingleton R M
    simp only [eq_iff_true_of_subsingleton]
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
#align module.subsingleton_equiv Module.subsingletonEquiv

def splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose
#align linear_map.splitting_of_finsupp_surjective LinearMap.splittingOfFinsuppSurjective

def splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R) (s : Surjective f) :
    (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap
#align linear_map.splitting_of_fun_on_fintype_surjective LinearMap.splittingOfFunOnFintypeSurjective

structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

In this file we define `Finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `LinearMap` versions of various maps:

* `Finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `Finsupp.single a` as a linear map;
* `Finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `fun f ↦ f a` as a linear map;
* `Finsupp.lsubtypeDomain (s : Set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;
* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;
* `Finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;
* `Finsupp.totalOn`: a restricted version of `Finsupp.total` with domain `Finsupp.supported R R s`
  and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.lmapDomain`: a linear map version of `Finsupp.mapDomain`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;
* `Finsupp.lcongr`: a `LinearEquiv`alence between `α →₀ M` and `β →₀ N` constructed using
  `e : α ≃ β` and `e' : M ≃ₗ[R] N`.

## Tags