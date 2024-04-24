def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B
    where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_nat addMonoidHomLequivNat

def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B
    where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_int addMonoidHomLequivInt

def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ => rfl }

/-! ### Properties of linear maps -/

def range [RingHomSurjective τ₁₂] (f : F) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
#align linear_map.range LinearMap.range

def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: #8386 changed `map_smulₛₗ` into `map_smulₛₗ _`

def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    rw [LinearMap.mem_range]
    use (f ^ c) m
    rw [pow_add, LinearMap.mul_apply]
#align linear_map.iterate_range LinearMap.iterateRange

def rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)
#align linear_map.range_restrict LinearMap.rangeRestrict

def MapSubtype.relIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simp [map_comap_subtype p, inf_of_le_right hq]
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans <| by
    dsimp
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]
#align submodule.map_subtype.rel_iso Submodule.MapSubtype.relIso

def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.relIso p).trans <|
    Subtype.relEmbedding (X := Submodule R M) (fun p p' ↦ p ≤ p') _
#align submodule.map_subtype.order_embedding Submodule.MapSubtype.orderEmbedding

def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ
#align linear_map.submodule_image LinearMap.submoduleImage

def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ => by
      ext
      rfl
    map_smul' := fun _ _ => by
      ext
      rfl }
#align linear_equiv.curry LinearEquiv.curry

def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equiv.Set.ofEq (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align linear_equiv.of_eq LinearEquiv.ofEq

def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)
#align linear_equiv.of_submodules LinearEquiv.ofSubmodules

def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ f.symm.map_eq_comap).symm
#align linear_equiv.of_submodule' LinearEquiv.ofSubmodule'

def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
#align linear_equiv.of_top LinearEquiv.ofTop

def ofLinear (h₁ : f.comp g = LinearMap.id) (h₂ : g.comp f = LinearMap.id) : M ≃ₛₗ[σ₁₂] M₂ :=
  { f with
    invFun := g
    left_inv := LinearMap.ext_iff.1 h₂
    right_inv := LinearMap.ext_iff.1 h₁ }
#align linear_equiv.of_linear LinearEquiv.ofLinear

def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ → M}
    (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f) :=
  { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align linear_equiv.of_left_inverse LinearEquiv.ofLeftInverse

def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] LinearMap.range f :=
  ofLeftInverse <| Classical.choose_spec h.hasLeftInverse
#align linear_equiv.of_injective LinearEquiv.ofInjective

def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans (ofTop _ <| LinearMap.range_eq_top.2 hf.surjective)
#align linear_equiv.of_bijective LinearEquiv.ofBijective

def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M →ₗ[R] M) with }
#align linear_equiv.neg LinearEquiv.neg

def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a
#align linear_equiv.smul_of_unit LinearEquiv.smulOfUnit

def arrowCongr {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁]
    [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) : (M₁ →ₗ[R] M₂₁) ≃ₗ[R] M₂ →ₗ[R] M₂₂
    where
  toFun := fun f : M₁ →ₗ[R] M₂₁ => (e₂ : M₂₁ →ₗ[R] M₂₂).comp <| f.comp (e₁.symm : M₂ →ₗ[R] M₁)
  invFun f := (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp <| f.comp (e₁ : M₁ →ₗ[R] M₂)
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]
  map_smul' c f := by
    ext x
    simp only [smul_apply, Function.comp_apply, coe_comp, map_smulₛₗ e₂, coe_coe]
#align linear_equiv.arrow_congr LinearEquiv.arrowCongr

def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f
#align linear_equiv.congr_right LinearEquiv.congrRight

def conj (e : M ≃ₗ[R] M₂) : Module.End R M ≃ₗ[R] Module.End R M₂ :=
  arrowCongr e e
#align linear_equiv.conj LinearEquiv.conj

def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.left_inv ·)
  right_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.right_inv ·)

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module K M] [Module K M₂] [Module K M₃]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha
#align linear_equiv.smul_of_ne_zero LinearEquiv.smulOfNeZero

def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.subtype :=
  { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine' ⟨⟨x, _⟩, _⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption
    left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    right_inv := fun ⟨x, ⟨_, h⟩, _, rfl⟩ => by ext; rfl }
#align submodule.equiv_subtype_map Submodule.equivSubtypeMap

def comap_equiv_self_of_inj_of_le {f : M →ₗ[R] N} {p : Submodule R N}
    (hf : Injective f) (h : p ≤ LinearMap.range f) :
    p.comap f ≃ₗ[R] p :=
  LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨x, hx⟩ ↦ mem_comap.mp hx)
  (⟨fun x y hxy ↦ by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ ↦ by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

end Module

end Submodule


namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }
#align equiv.to_linear_equiv Equiv.toLinearEquiv

def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.fun_left LinearMap.funLeft

def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])
#align linear_equiv.fun_congr_left LinearEquiv.funCongrLeft