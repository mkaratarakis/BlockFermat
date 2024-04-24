def fst : M × M₂ →ₗ[R] M where
  toFun := Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl
#align linear_map.fst LinearMap.fst

def snd : M × M₂ →ₗ[R] M₂ where
  toFun := Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl
#align linear_map.snd LinearMap.snd

def prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ where
  toFun := Pi.prod f g
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Pi.prod, Prod.smul_mk, map_smul, RingHom.id_apply]
#align linear_map.prod LinearMap.prod

def prodEquiv [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₂) × (M →ₗ[R] M₃)) ≃ₗ[S] M →ₗ[R] M₂ × M₃ where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
  map_add' a b := rfl
  map_smul' r a := rfl
#align linear_map.prod_equiv LinearMap.prodEquiv

def inl : M →ₗ[R] M × M₂ :=
  prod LinearMap.id 0
#align linear_map.inl LinearMap.inl

def inr : M₂ →ₗ[R] M × M₂ :=
  prod 0 LinearMap.id
#align linear_map.inr LinearMap.inr

def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
  f.comp (fst _ _ _) + g.comp (snd _ _ _)
#align linear_map.coprod LinearMap.coprod

def coprodEquiv [Module S M₃] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] M × M₂ →ₗ[R] M₃
    where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, Prod.smul_snd, Prod.smul_fst, coprod_apply]
#align linear_map.coprod_equiv LinearMap.coprodEquiv

def prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : M × M₂ →ₗ[R] M₃ × M₄ :=
  (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))
#align linear_map.prod_map LinearMap.prodMap

def prodMapLinear [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulCommClass R S M₄] :
    (M →ₗ[R] M₃) × (M₂ →ₗ[R] M₄) →ₗ[S] M × M₂ →ₗ[R] M₃ × M₄
    where
  toFun f := prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.prod_map_linear LinearMap.prodMapLinear

def prodMapRingHom : (M →ₗ[R] M) × (M₂ →ₗ[R] M₂) →+* M × M₂ →ₗ[R] M × M₂
    where
  toFun f := prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align linear_map.prod_map_ring_hom LinearMap.prodMapRingHom

def prodMapAlgHom : Module.End R M × Module.End R M₂ →ₐ[R] Module.End R (M × M₂) :=
  { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }
#align linear_map.prod_map_alg_hom LinearMap.prodMapAlgHom

def fst : Submodule R (M × M₂) :=
  (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)
#align submodule.fst Submodule.fst

def fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where
  -- Porting note: proofs were `tidy` or `simp`
  toFun x := x.1.1
  invFun m := ⟨⟨m, 0⟩, by simp only [fst, comap_bot, mem_ker, snd_apply]⟩
  map_add' := by simp only [AddSubmonoid.coe_add, coe_toAddSubmonoid, Prod.fst_add, Subtype.forall,
    implies_true, Prod.forall, forall_const]
  map_smul' := by simp only [SetLike.val_smul, Prod.smul_fst, RingHom.id_apply, Subtype.forall,
    implies_true, Prod.forall, forall_const]
  left_inv := by
    rintro ⟨⟨x, y⟩, hy⟩
    simp only [fst, comap_bot, mem_ker, snd_apply] at hy
    simpa only [Subtype.mk.injEq, Prod.mk.injEq, true_and] using hy.symm
  right_inv := by rintro x; rfl
#align submodule.fst_equiv Submodule.fstEquiv

def snd : Submodule R (M × M₂) :=
  (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)
#align submodule.snd Submodule.snd

def sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
  -- Porting note: proofs were `tidy` or `simp`
  toFun x := x.1.2
  invFun n := ⟨⟨0, n⟩, by simp only [snd, comap_bot, mem_ker, fst_apply]⟩
  map_add' := by simp only [AddSubmonoid.coe_add, coe_toAddSubmonoid, Prod.snd_add, Subtype.forall,
    implies_true, Prod.forall, forall_const]
  map_smul' := by simp only [SetLike.val_smul, Prod.smul_snd, RingHom.id_apply, Subtype.forall,
    implies_true, Prod.forall, forall_const]
  left_inv := by
    rintro ⟨⟨x, y⟩, hx⟩
    simp only [snd, comap_bot, mem_ker, fst_apply] at hx
    simpa only [Subtype.mk.injEq, Prod.mk.injEq, and_true] using hx.symm
  right_inv := by rintro x; rfl
#align submodule.snd_equiv Submodule.sndEquiv

def prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] : (M × N) ≃ₗ[R] N × M :=
  { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }
#align linear_equiv.prod_comm LinearEquiv.prodComm

def prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄ :=
  { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }
#align linear_equiv.prod_prod_prod_comm LinearEquiv.prodProdProdComm

def prod : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }
#align linear_equiv.prod LinearEquiv.prod

def skewProd (f : M →ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { ((e₁ : M →ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ →ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }
#align linear_equiv.skew_prod LinearEquiv.skewProd

def tunnelAux (f : M × N →ₗ[R] M) (Kφ : ΣK : Submodule R M, K ≃ₗ[R] M) : M × N →ₗ[R] M :=
  (Kφ.1.subtype.comp Kφ.2.symm.toLinearMap).comp f
#align linear_map.tunnel_aux LinearMap.tunnelAux

def tunnel' (f : M × N →ₗ[R] M) (i : Injective f) : ℕ → ΣK : Submodule R M, K ≃ₗ[R] M
  | 0 => ⟨⊤, LinearEquiv.ofTop ⊤ rfl⟩
  | n + 1 =>
    ⟨(Submodule.fst R M N).map (tunnelAux f (tunnel' f i n)),
      ((Submodule.fst R M N).equivMapOfInjective _
        (tunnelAux_injective f i (tunnel' f i n))).symm.trans (Submodule.fstEquiv R M N)⟩
#align linear_map.tunnel' LinearMap.tunnel'ₓ -- Porting note: different universes

def tunnel (f : M × N →ₗ[R] M) (i : Injective f) : ℕ →o (Submodule R M)ᵒᵈ :=
  -- Note: the hint `(α := _)` had to be added in #8386

def tailing (f : M × N →ₗ[R] M) (i : Injective f) (n : ℕ) : Submodule R M :=
  (Submodule.snd R M N).map (tunnelAux f (tunnel' f i n))
#align linear_map.tailing LinearMap.tailing

def tailingLinearEquiv (f : M × N →ₗ[R] M) (i : Injective f) (n : ℕ) : tailing f i n ≃ₗ[R] N :=
  ((Submodule.snd R M N).equivMapOfInjective _ (tunnelAux_injective f i (tunnel' f i n))).symm.trans
    (Submodule.sndEquiv R M N)
#align linear_map.tailing_linear_equiv LinearMap.tailingLinearEquiv

def tailings (f : M × N →ₗ[R] M) (i : Injective f) : ℕ → Submodule R M :=
  partialSups (tailing f i)
#align linear_map.tailings LinearMap.tailings

def graph : Submodule R (M × M₂)
    where
  carrier := { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add, ha, hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul, hx]
#align linear_map.graph LinearMap.graph