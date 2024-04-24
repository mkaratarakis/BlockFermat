def subtype : S' →ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align submodule_class.subtype SMulMemClass.subtype

def subtype : p →ₗ[R] M := by refine' { toFun := Subtype.val.. } <;> simp [coe_smul]
#align submodule.subtype Submodule.subtype

def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype
#align linear_map.dom_restrict LinearMap.domRestrict

def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p := by
  refine' { toFun := fun c => ⟨f c, h c⟩.. } <;> intros <;> apply SetCoe.ext <;> simp
#align linear_map.cod_restrict LinearMap.codRestrict

def restrict (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₗ[R] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf
#align linear_map.restrict LinearMap.restrict

def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl
#align linear_map.eval_add_monoid_hom LinearMap.evalAddMonoidHom

def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl
#align linear_map.to_add_monoid_hom' LinearMap.toAddMonoidHom'

def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂ where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]
#align linear_map.dom_restrict' LinearMap.domRestrict'

def inclusion (h : p ≤ p') : p →ₗ[R] p' :=
  p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx
#align submodule.of_le Submodule.inclusion

structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M := by refine' { toFun := Subtype.val.. } <;> simp [coe_smul]
#align submodule.subtype Submodule.subtype