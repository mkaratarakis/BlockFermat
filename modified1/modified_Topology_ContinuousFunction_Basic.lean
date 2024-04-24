def toContinuousMap (f : F) : C(α, β) := ⟨f, map_continuous f⟩

instance : CoeTC F C(α, β) := ⟨toContinuousMap⟩

end ContinuousMapClass

/-! ### Continuous maps-/

def Simps.apply (f : C(α, β)) : α → β := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[simp] -- Porting note: removed `norm_cast` attribute
protected theorem coe_coe {F : Type*} [FunLike F α β] [ContinuousMapClass F α β] (f : F) :
    ⇑(f : C(α, β)) = f :=
  rfl
#align continuous_map.coe_coe ContinuousMap.coe_coe

def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β) where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun
#align continuous_map.copy ContinuousMap.copy

def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩
#align continuous_map.equiv_fn_of_discrete ContinuousMap.equivFnOfDiscrete

def id : C(α, α) where
  toFun := id
#align continuous_map.id ContinuousMap.id

def const (b : β) : C(α, β) where
  toFun := fun _ : α => b
#align continuous_map.const ContinuousMap.const

def constPi : C(β, α → β) where
  toFun b := Function.const α b

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl
#align continuous_map.id_apply ContinuousMap.id_apply

def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g
#align continuous_map.comp ContinuousMap.comp

def fst : C(α × β, α) where
  toFun := Prod.fst

/-- `Prod.snd : (x, y) ↦ y` as a bundled continuous map. -/
@[simps (config := .asFn)]
def snd : C(α × β, β) where
  toFun := Prod.snd

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)
#align continuous_map.prod_mk ContinuousMap.prodMk

def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g
  continuous_toFun := f.continuous.prod_map g.continuous
  -- Porting note: proof was `continuity`
#align continuous_map.prod_map ContinuousMap.prodMap

def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

section Sigma

variable {I A : Type*} {X : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

/--
To give a continuous map out of a disjoint union, it suffices to give a continuous map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
@[simps]
def sigma (f : ∀ i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
@[simps]
def sigmaEquiv : (∀ i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

end Sigma

section Pi

variable {I A : Type*} {X Y : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun (a : A) (i : I) := f i a
#align continuous_map.pi ContinuousMap.pi

def eval (i : I) : C(∀ j, X j, X i) where
  toFun := Function.eval i

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term
-/
@[simps]
def piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f
  left_inv := by intro; ext; simp [pi]
  right_inv := by intro; ext; simp [pi]

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

/-- "Precomposition" as a continuous map between dependent types. -/
def precomp {ι : Type*} (φ : ι → I) : C((i : I) → X i, (i : ι) → X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s → α)
#align continuous_map.restrict ContinuousMap.restrict

def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ => f.2.continuousAt.restrictPreimage⟩
#align continuous_map.restrict_preimage ContinuousMap.restrictPreimage

def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_restrict]
    simpa (config := { unfoldPartialApp := true }) only [Set.restrict, Set.liftCover_coe] using
      (φ i).continuous
#align continuous_map.lift_cover ContinuousMap.liftCover

def liftCover' : C(α, β) := by
  let S : A → Set α := (↑)
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  refine' liftCover S F (fun i j => hF i i.prop j j.prop) _
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩
#align continuous_map.lift_cover' ContinuousMap.liftCover'

def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr f.continuous
  continuous_invFun := continuous_quotient_mk'.comp f'.continuous

namespace QuotientMap

/--
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
@[simps!]
noncomputable def homeomorph (hf : QuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : QuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

/-- Descend a continuous map, which is constant on the fibres, along a quotient map. -/
@[simps]
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i ↦ Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) ↦ h hab)) :
    Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

/--
The obvious triangle induced by `QuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
@[simp]
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

/-- `QuotientMap.lift` as an equivalence. -/
@[simps]
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h ↦ by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end QuotientMap

end Lift

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps]
def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous_toFun⟩
#align homeomorph.to_continuous_map Homeomorph.toContinuousMap

structure ContinuousMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  /-- The function `α → β` -/
  protected toFun : α → β
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by continuity
#align continuous_map ContinuousMap