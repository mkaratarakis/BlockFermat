def map (f : F) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }
#align submodule.map Submodule.map

def equivMapOfInjective (f : F) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: #8386 changed `map_smulₛₗ` into `map_smulₛₗ _`

def comap (f : F) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: #8386 added `map_smulₛₗ _`

def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩
#align submodule.gi_map_comap Submodule.giMapComap

def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]
#align submodule.gci_map_comap Submodule.gciMapComap

def orderIsoMapComapOfBijective [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
    (f : F) (hf : Bijective f) : Submodule R M ≃o Submodule R₂ M₂ where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps! symm_apply apply]
def orderIsoMapComap [EquivLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂] (f : F) :
    Submodule R M ≃o Submodule R₂ M₂ := orderIsoMapComapOfBijective f (EquivLike.bijective f)
#align submodule.order_iso_map_comap Submodule.orderIsoMapComap

def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.subtype p ≃ₗ[R] p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp only [coe_mk, SetLike.eta, LinearEquiv.coe_coe]
  right_inv x := by simp only [Subtype.coe_mk, SetLike.eta, LinearEquiv.coe_coe]
  map_add' x y := rfl
  map_smul' c x := rfl
#align submodule.comap_subtype_equiv_of_le Submodule.comapSubtypeEquivOfLe

def compatibleMaps : Submodule R (N →ₗ[R] N₂) where
  carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by
    change pₗ ≤ comap (0 : N →ₗ[R] N₂) qₗ
    rw [comap_zero]
    exact le_top
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)
#align submodule.compatible_maps Submodule.compatibleMaps

def submoduleMap (f : M →ₗ[R] M₁) (p : Submodule R M) : p →ₗ[R] p.map f :=
  f.restrict fun x hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
theorem submoduleMap_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} (x : p) :
    ↑(f.submoduleMap p x) = f x := rfl

theorem submoduleMap_surjective (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Function.Surjective (f.submoduleMap p) := f.toAddMonoidHom.addSubmonoidMap_surjective _

variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₂₁ : R₂ →+* R}

open Submodule

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff_val]
#align linear_map.map_cod_restrict LinearMap.map_codRestrict

def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, eq_self_iff_true, and_true_iff, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, Submodule.coe_mk, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }
#align linear_equiv.submodule_map LinearEquiv.submoduleMap