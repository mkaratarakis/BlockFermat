def UniformFun (α β : Type*) :=
  α → β
#align uniform_fun UniformFun

def UniformOnFun (α β : Type*) (_ : Set (Set α)) :=
  α → β
#align uniform_on_fun UniformOnFun

def UniformFun.ofFun : (α → β) ≃ (α →ᵤ β) :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align uniform_fun.of_fun UniformFun.ofFun

def UniformOnFun.ofFun (𝔖) : (α → β) ≃ (α →ᵤ[𝔖] β) :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align uniform_on_fun.of_fun UniformOnFun.ofFun

def UniformFun.toFun : (α →ᵤ β) ≃ (α → β) :=
  UniformFun.ofFun.symm
#align uniform_fun.to_fun UniformFun.toFun

def UniformOnFun.toFun (𝔖) : (α →ᵤ[𝔖] β) ≃ (α → β) :=
  (UniformOnFun.ofFun 𝔖).symm
#align uniform_on_fun.to_fun UniformOnFun.toFun

def gen (V : Set (β × β)) : Set ((α →ᵤ β) × (α →ᵤ β)) :=
  { uv : (α →ᵤ β) × (α →ᵤ β) | ∀ x, (toFun uv.1 x, toFun uv.2 x) ∈ V }
#align uniform_fun.gen UniformFun.gen

def basis (𝓕 : Filter <| β × β) : FilterBasis ((α →ᵤ β) × (α →ᵤ β)) :=
  (UniformFun.isBasis_gen α β 𝓕).filterBasis
#align uniform_fun.basis UniformFun.basis

def filter (𝓕 : Filter <| β × β) : Filter ((α →ᵤ β) × (α →ᵤ β)) :=
  (UniformFun.basis α β 𝓕).filter
#align uniform_fun.filter UniformFun.filter

def phi (α β : Type*) (uvx : ((α →ᵤ β) × (α →ᵤ β)) × α) : β × β :=
  (uvx.fst.fst uvx.2, uvx.1.2 uvx.2)

set_option quotPrecheck false -- Porting note: error message suggested to do this
/- This is a lower adjoint to `UniformFun.filter` (see `UniformFun.gc`).
The exact definition of the lower adjoint `l` is not interesting; we will only use that it exists
(in `UniformFun.mono` and `UniformFun.iInf_eq`) and that
`l (Filter.map (Prod.map f f) 𝓕) = Filter.map (Prod.map ((∘) f) ((∘) f)) (l 𝓕)` for each
`𝓕 : Filter (γ × γ)` and `f : γ → α` (in `UniformFun.comap_eq`). -/
local notation "lowerAdjoint" => fun 𝓐 => map (UniformFun.phi α β) (𝓐 ×ˢ ⊤)

/-- The function `UniformFun.filter α β : Filter (β × β) → Filter ((α →ᵤ β) × (α →ᵤ β))`
has a lower adjoint `l` (in the sense of `GaloisConnection`). The exact definition of `l` is not
interesting; we will only use that it exists (in `UniformFun.mono` and
`UniformFun.iInf_eq`) and that
`l (Filter.map (Prod.map f f) 𝓕) = Filter.map (Prod.map ((∘) f) ((∘) f)) (l 𝓕)` for each
`𝓕 : Filter (γ × γ)` and `f : γ → α` (in `UniformFun.comap_eq`). -/
protected theorem gc : GaloisConnection lowerAdjoint fun 𝓕 => UniformFun.filter α β 𝓕 := by
  intro 𝓐 𝓕
  symm
  calc
    𝓐 ≤ UniformFun.filter α β 𝓕 ↔ (UniformFun.basis α β 𝓕).sets ⊆ 𝓐.sets :=
      by rw [UniformFun.filter, ← FilterBasis.generate, le_generate_iff]
    _ ↔ ∀ U ∈ 𝓕, UniformFun.gen α β U ∈ 𝓐 := image_subset_iff
    _ ↔ ∀ U ∈ 𝓕,
          { uv | ∀ x, (uv, x) ∈ { t : ((α →ᵤ β) × (α →ᵤ β)) × α | (t.1.1 t.2, t.1.2 t.2) ∈ U } } ∈
            𝓐 :=
      Iff.rfl
    _ ↔ ∀ U ∈ 𝓕,
          { uvx : ((α →ᵤ β) × (α →ᵤ β)) × α | (uvx.1.1 uvx.2, uvx.1.2 uvx.2) ∈ U } ∈
            𝓐 ×ˢ (⊤ : Filter α) :=
      forall₂_congr fun U _hU => mem_prod_top.symm
    _ ↔ lowerAdjoint 𝓐 ≤ 𝓕 := Iff.rfl
#align uniform_fun.gc UniformFun.gc

def uniformCore : UniformSpace.Core (α →ᵤ β) :=
  UniformSpace.Core.mkOfBasis (UniformFun.basis α β (𝓤 β))
    (fun _ ⟨_, hV, hVU⟩ _ => hVU ▸ fun _ => refl_mem_uniformity hV)
    (fun _ ⟨V, hV, hVU⟩ =>
      hVU ▸
        ⟨UniformFun.gen α β (Prod.swap ⁻¹' V), ⟨Prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩,
          fun _ huv x => huv x⟩)
    fun _ ⟨_, hV, hVU⟩ =>
    hVU ▸
      let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
      ⟨UniformFun.gen α β W, ⟨W, hW, rfl⟩, fun _ ⟨w, huw, hwv⟩ x => hWV ⟨w x, ⟨huw x, hwv x⟩⟩⟩
#align uniform_fun.uniform_core UniformFun.uniformCore

def congrRight [UniformSpace γ] (e : γ ≃ᵤ β) : (α →ᵤ γ) ≃ᵤ (α →ᵤ β) :=
  { Equiv.piCongrRight fun _ => e.toEquiv with
    uniformContinuous_toFun := UniformFun.postcomp_uniformContinuous e.uniformContinuous
    uniformContinuous_invFun := UniformFun.postcomp_uniformContinuous e.symm.uniformContinuous }
#align uniform_fun.congr_right UniformFun.congrRight

def congrLeft (e : γ ≃ α) : (γ →ᵤ β) ≃ᵤ (α →ᵤ β) where
  toEquiv := e.arrowCongr (.refl _)
  uniformContinuous_toFun := UniformFun.precomp_uniformContinuous
  uniformContinuous_invFun := UniformFun.precomp_uniformContinuous
#align uniform_fun.congr_left UniformFun.congrLeft

def uniformEquivProdArrow [UniformSpace γ] : (α →ᵤ β × γ) ≃ᵤ (α →ᵤ β) × (α →ᵤ γ) :=
  -- Denote `φ` this bijection. We want to show that
  -- `comap φ (𝒰(α, β, uβ) × 𝒰(α, γ, uγ)) = 𝒰(α, β × γ, uβ × uγ)`.
  -- But `uβ × uγ` is defined as `comap fst uβ ⊓ comap snd uγ`, so we just have to apply
  -- `UniformFun.inf_eq` and `UniformFun.comap_eq`, which leaves us to check
  -- that some square commutes.
  Equiv.toUniformEquivOfUniformInducing (Equiv.arrowProdEquivProdArrow _ _ _) <| by
    constructor
    change
      comap (Prod.map (Equiv.arrowProdEquivProdArrow _ _ _) (Equiv.arrowProdEquivProdArrow _ _ _))
          _ = _
    simp_rw [UniformFun]
    rw [← uniformity_comap]
    congr
    unfold instUniformSpaceProd
    rw [UniformSpace.comap_inf, ← UniformSpace.comap_comap, ← UniformSpace.comap_comap]
    have := (@UniformFun.inf_eq α (β × γ)
      (UniformSpace.comap Prod.fst ‹_›) (UniformSpace.comap Prod.snd ‹_›)).symm
    rwa [UniformFun.comap_eq, UniformFun.comap_eq] at this
#align uniform_fun.uniform_equiv_prod_arrow UniformFun.uniformEquivProdArrow

def uniformEquivPiComm : UniformEquiv (α →ᵤ ∀ i, δ i) (∀ i, α →ᵤ δ i) :=
  -- Denote `φ` this bijection. We want to show that
    -- `comap φ (Π i, 𝒰(α, δ i, uδ i)) = 𝒰(α, (Π i, δ i), (Π i, uδ i))`.
    -- But `Π i, uδ i` is defined as `⨅ i, comap (eval i) (uδ i)`, so we just have to apply
    -- `UniformFun.iInf_eq` and `UniformFun.comap_eq`, which leaves us to check
    -- that some square commutes.
    @Equiv.toUniformEquivOfUniformInducing
    _ _ 𝒰(α, ∀ i, δ i, Pi.uniformSpace δ)
    (@Pi.uniformSpace ι (fun i => α → δ i) fun i => 𝒰(α, δ i, _)) (Equiv.piComm _) <| by
      refine @UniformInducing.mk ?_ ?_ ?_ ?_ ?_ ?_
      change comap (Prod.map Function.swap Function.swap) _ = _
      rw [← uniformity_comap]
      congr
      unfold Pi.uniformSpace
      rw [UniformSpace.ofCoreEq_toCore, UniformSpace.ofCoreEq_toCore,
        UniformSpace.comap_iInf, UniformFun.iInf_eq]
      refine' iInf_congr fun i => _
      rw [← UniformSpace.comap_comap, UniformFun.comap_eq]
      rfl
#align uniform_fun.uniform_equiv_Pi_comm UniformFun.uniformEquivPiComm

def gen (𝔖) (S : Set α) (V : Set (β × β)) : Set ((α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] β)) :=
  { uv : (α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] β) | ∀ x ∈ S, (toFun 𝔖 uv.1 x, toFun 𝔖 uv.2 x) ∈ V }
#align uniform_on_fun.gen UniformOnFun.gen

def congrRight [UniformSpace γ] (e : γ ≃ᵤ β) : (α →ᵤ[𝔖] γ) ≃ᵤ (α →ᵤ[𝔖] β) :=
  { Equiv.piCongrRight fun _a => e.toEquiv with
    uniformContinuous_toFun := UniformOnFun.postcomp_uniformContinuous e.uniformContinuous
    uniformContinuous_invFun := UniformOnFun.postcomp_uniformContinuous e.symm.uniformContinuous }
#align uniform_on_fun.congr_right UniformOnFun.congrRight

def congrLeft {𝔗 : Set (Set γ)} (e : γ ≃ α) (he : 𝔗 ⊆ image e ⁻¹' 𝔖)
    (he' : 𝔖 ⊆ preimage e ⁻¹' 𝔗) : (γ →ᵤ[𝔗] β) ≃ᵤ (α →ᵤ[𝔖] β) :=
  { Equiv.arrowCongr e (Equiv.refl _) with
    uniformContinuous_toFun := UniformOnFun.precomp_uniformContinuous fun s hs ↦ by
      change e.symm '' s ∈ 𝔗
      rw [← preimage_equiv_eq_image_symm]
      exact he' hs
    uniformContinuous_invFun := UniformOnFun.precomp_uniformContinuous he }
#align uniform_on_fun.congr_left UniformOnFun.congrLeft

def uniformEquivProdArrow [UniformSpace γ] :
    (α →ᵤ[𝔖] β × γ) ≃ᵤ (α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] γ) :=
  -- Denote `φ` this bijection. We want to show that
  -- `comap φ (𝒱(α, β, 𝔖, uβ) × 𝒱(α, γ, 𝔖, uγ)) = 𝒱(α, β × γ, 𝔖, uβ × uγ)`.
  -- But `uβ × uγ` is defined as `comap fst uβ ⊓ comap snd uγ`, so we just have to apply
  -- `UniformOnFun.inf_eq` and `UniformOnFun.comap_eq`,
  -- which leaves us to check that some square commutes.
  -- We could also deduce this from `UniformFun.uniformEquivProdArrow`,
  -- but it turns out to be more annoying.
  ((UniformOnFun.ofFun 𝔖).symm.trans <|
    (Equiv.arrowProdEquivProdArrow _ _ _).trans <|
      (UniformOnFun.ofFun 𝔖).prodCongr (UniformOnFun.ofFun 𝔖)).toUniformEquivOfUniformInducing <| by
      constructor
      rw [uniformity_prod, comap_inf, comap_comap, comap_comap]
      have H := @UniformOnFun.inf_eq α (β × γ) 𝔖
        (UniformSpace.comap Prod.fst ‹_›) (UniformSpace.comap Prod.snd ‹_›)
      apply_fun (fun u ↦ @uniformity (α →ᵤ[𝔖] β × γ) u) at H
      convert H.symm using 1
      rw [UniformOnFun.comap_eq, UniformOnFun.comap_eq]
      erw [inf_uniformity]
      rw [uniformity_comap, uniformity_comap]
      rfl
#align uniform_on_fun.uniform_equiv_prod_arrow UniformOnFun.uniformEquivProdArrow

def uniformEquivPiComm : (α →ᵤ[𝔖] ((i:ι) → δ i)) ≃ᵤ ((i:ι) → α →ᵤ[𝔖] δ i) :=
  -- Denote `φ` this bijection. We want to show that
  -- `comap φ (Π i, 𝒱(α, δ i, 𝔖, uδ i)) = 𝒱(α, (Π i, δ i), 𝔖, (Π i, uδ i))`.
  -- But `Π i, uδ i` is defined as `⨅ i, comap (eval i) (uδ i)`, so we just have to apply
  -- `UniformOnFun.iInf_eq` and `UniformOnFun.comap_eq`,
  -- which leaves us to check that some square commutes.
  -- We could also deduce this from `UniformFun.uniformEquivPiComm`, but it turns out
  -- to be more annoying.
  @Equiv.toUniformEquivOfUniformInducing (α →ᵤ[𝔖] ((i:ι) → δ i)) ((i:ι) → α →ᵤ[𝔖] δ i)
      _ _ (Equiv.piComm _) <| by
    constructor
    change comap (Prod.map Function.swap Function.swap) _ = _
    erw [← uniformity_comap]
    congr
    rw [Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, Pi.uniformSpace,
      UniformSpace.ofCoreEq_toCore, UniformSpace.comap_iInf, UniformOnFun.iInf_eq]
    refine' iInf_congr fun i => _
    rw [← UniformSpace.comap_comap, UniformOnFun.comap_eq]
    rfl
#align uniform_on_fun.uniform_equiv_Pi_comm UniformOnFun.uniformEquivPiComm

structure of uniform convergence

This files endows `α → β` with the topologies / uniform structures of
- uniform convergence on `α`
- uniform convergence on a specified family `𝔖` of sets of `α`, also called `𝔖`-convergence

Since `α → β` is already endowed with the topologies and uniform structures of pointwise
convergence, we introduce type aliases `UniformFun α β` (denoted `α →ᵤ β`) and
`UniformOnFun α β 𝔖` (denoted `α →ᵤ[𝔖] β`) and we actually endow *these* with the structures
of uniform and `𝔖`-convergence respectively.

Usual examples of the second construction include :
- the topology of compact convergence, when `𝔖` is the set of compacts of `α`
- the strong topology on the dual of a topological vector space (TVS) `E`, when `𝔖` is the set of
  Von Neumann bounded subsets of `E`
- the weak-* topology on the dual of a TVS `E`, when `𝔖` is the set of singletons of `E`.

This file contains a lot of technical facts, so it is heavily commented, proofs included!

## Main definitions

structure of uniform convergence. This is the
  `UniformSpace` on `α →ᵤ β` whose uniformity is generated by the sets `S(V)` for `V ∈ 𝓤 β`.
  We will denote this uniform space as `𝒰(α, β, uβ)`, both in the comments and as a local notation
  in the Lean code, where `uβ` is the uniform space structure on `β`.
  This is declared as an instance on `α →ᵤ β`.
* `UniformOnFun.uniformSpace`: uniform structure of `𝔖`-convergence, where
  `𝔖 : Set (Set α)`. This is the infimum, for `S ∈ 𝔖`, of the pullback of `𝒰 S β` by the map of
  restriction to `S`. We will denote it `𝒱(α, β, 𝔖, uβ)`, where `uβ` is the uniform space structure
  on `β`.
  This is declared as an instance on `α →ᵤ[𝔖] β`.

## Main statements

structure of uniform convergence
* `UniformOnFun.uniformContinuous_eval_of_mem`: evaluation at a point contained in a
  set of `𝔖` is uniformly continuous on `α →ᵤ[𝔖] β`
* `UniformOnFun.t2Space_of_covering`: the topology of `𝔖`-convergence on `α →ᵤ[𝔖] β` is T₂ if
  `β` is T₂ and `𝔖` covers `α`
* `UniformOnFun.tendsto_iff_tendstoUniformlyOn`:
  `𝒱(α, β, 𝔖 uβ)` is indeed the uniform structure of `𝔖`-convergence

### Functoriality and compatibility with product of uniform spaces

structure of uniform convergence! Instead, we build a
(not very interesting) Galois connection `UniformFun.gc` and then rely on the Galois
connection API to do most of the work.

#### Morphism statements (unbundled)

structure of `𝔖`-convergence is exactly the structure of `𝔖'`-convergence,
  where `𝔖'` is the ***noncovering*** bornology (i.e ***not*** what `Bornology` currently refers
  to in mathlib) generated by `𝔖`.

## References

structure and topology of
uniform convergence. We denote it `α →ᵤ β`. -/
def UniformFun (α β : Type*) :=
  α → β
#align uniform_fun UniformFun

structure and topology of
uniform convergence on some family `𝔖` of subsets of `α`. We denote it `α →ᵤ[𝔖] β`. -/
@[nolint unusedArguments]
def UniformOnFun (α β : Type*) (_ : Set (Set α)) :=
  α → β
#align uniform_on_fun UniformOnFun

structure of uniform convergence. -/
protected def uniformCore : UniformSpace.Core (α →ᵤ β) :=
  UniformSpace.Core.mkOfBasis (UniformFun.basis α β (𝓤 β))
    (fun _ ⟨_, hV, hVU⟩ _ => hVU ▸ fun _ => refl_mem_uniformity hV)
    (fun _ ⟨V, hV, hVU⟩ =>
      hVU ▸
        ⟨UniformFun.gen α β (Prod.swap ⁻¹' V), ⟨Prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩,
          fun _ huv x => huv x⟩)
    fun _ ⟨_, hV, hVU⟩ =>
    hVU ▸
      let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
      ⟨UniformFun.gen α β W, ⟨W, hW, rfl⟩, fun _ ⟨w, huw, hwv⟩ x => hWV ⟨w x, ⟨huw x, hwv x⟩⟩⟩
#align uniform_fun.uniform_core UniformFun.uniformCore

structure of uniform convergence, declared as an instance on `α →ᵤ β`.
We will denote it `𝒰(α, β, uβ)` in the rest of this file. -/
instance uniformSpace : UniformSpace (α →ᵤ β) :=
  UniformSpace.ofCore (UniformFun.uniformCore α β)

/-- Topology of uniform convergence, declared as an instance on `α →ᵤ β`. -/
instance topologicalSpace : TopologicalSpace (α →ᵤ β) :=
  inferInstance

local notation "𝒰(" α ", " β ", " u ")" => @UniformFun.uniformSpace α β u

/-- By definition, the uniformity of `α →ᵤ β` admits the family `{(f, g) | ∀ x, (f x, g x) ∈ V}`
for `V ∈ 𝓤 β` as a filter basis. -/
protected theorem hasBasis_uniformity :
    (𝓤 (α →ᵤ β)).HasBasis (· ∈ 𝓤 β) (UniformFun.gen α β) :=
  (UniformFun.isBasis_gen α β (𝓤 β)).hasBasis
#align uniform_fun.has_basis_uniformity UniformFun.hasBasis_uniformity

structure of uniform convergence is finer than that of pointwise
convergence, aka the product uniform structure. -/
protected theorem uniformContinuous_toFun : UniformContinuous (toFun : (α →ᵤ β) → α → β) := by
  -- By definition of the product uniform structure, this is just `uniform_continuous_eval`.
  rw [uniformContinuous_pi]
  intro x
  exact uniformContinuous_eval β x
#align uniform_fun.uniform_continuous_to_fun UniformFun.uniformContinuous_toFun

structure of `𝔖`-convergence, as defined in `UniformOnFun.uniformSpace`. -/
protected theorem gen_eq_preimage_restrict {𝔖} (S : Set α) (V : Set (β × β)) :
    UniformOnFun.gen 𝔖 S V =
      Prod.map (S.restrict ∘ UniformFun.toFun) (S.restrict ∘ UniformFun.toFun) ⁻¹'
        UniformFun.gen S β V := by
  ext uv
  exact ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩
#align uniform_on_fun.gen_eq_preimage_restrict UniformOnFun.gen_eq_preimage_restrict

structure of `𝔖`-convergence, i.e uniform convergence on the elements of `𝔖`,
declared as an instance on `α →ᵤ[𝔖] β`. It is defined as the infimum, for `S ∈ 𝔖`, of the pullback
by `S.restrict`, the map of restriction to `S`, of the uniform structure `𝒰(s, β, uβ)` on
`↥S →ᵤ β`. We will denote it `𝒱(α, β, 𝔖, uβ)`, where `uβ` is the uniform structure on `β`. -/
instance uniformSpace : UniformSpace (α →ᵤ[𝔖] β) :=
  ⨅ (s : Set α) (_ : s ∈ 𝔖), UniformSpace.comap s.restrict 𝒰(s, β, _)

local notation "𝒱(" α ", " β ", " 𝔖 ", " u ")" => @UniformOnFun.uniformSpace α β u 𝔖

/-- Topology of `𝔖`-convergence, i.e uniform convergence on the elements of `𝔖`, declared as an
instance on `α →ᵤ[𝔖] β`. -/
instance topologicalSpace : TopologicalSpace (α →ᵤ[𝔖] β) :=
  𝒱(α, β, 𝔖, _).toTopologicalSpace

/-- The topology of `𝔖`-convergence is the infimum, for `S ∈ 𝔖`, of topology induced by the map
of `S.restrict : (α →ᵤ[𝔖] β) → (↥S →ᵤ β)` of restriction to `S`, where `↥S →ᵤ β` is endowed with
the topology of uniform convergence. -/
protected theorem topologicalSpace_eq :
    UniformOnFun.topologicalSpace α β 𝔖 =
      ⨅ (s : Set α) (_ : s ∈ 𝔖), TopologicalSpace.induced
        (UniformFun.ofFun ∘ s.restrict ∘ toFun 𝔖) (UniformFun.topologicalSpace s β) := by
  simp only [UniformOnFun.topologicalSpace, UniformSpace.toTopologicalSpace_iInf]
  rfl
#align uniform_on_fun.topological_space_eq UniformOnFun.topologicalSpace_eq

structure on `β` and `f : γ → β`, then
`𝒱(α, γ, 𝔖, comap f u) = comap (fun g ↦ f ∘ g) 𝒱(α, γ, 𝔖, u₁)`. -/
protected theorem comap_eq {f : γ → β} :
    𝒱(α, γ, 𝔖, ‹UniformSpace β›.comap f) = 𝒱(α, β, 𝔖, _).comap (f ∘ ·) := by
  -- We reduce this to `UniformFun.comap_eq` using the fact that `comap` distributes
  -- on `iInf`.
  simp_rw [UniformOnFun.uniformSpace, UniformSpace.comap_iInf, UniformFun.comap_eq, ←
    UniformSpace.comap_comap]
  rfl
#align uniform_on_fun.comap_eq UniformOnFun.comap_eq

structure of `𝔖`-convergence is finer than
that of pointwise convergence. -/
protected theorem uniformContinuous_toFun (h : ⋃₀ 𝔖 = univ) :
    UniformContinuous (toFun 𝔖 : (α →ᵤ[𝔖] β) → α → β) := by
  rw [uniformContinuous_pi]
  intro x
  obtain ⟨s : Set α, hs : s ∈ 𝔖, hxs : x ∈ s⟩ := sUnion_eq_univ_iff.mp h x
  exact uniformContinuous_eval_of_mem β 𝔖 hxs hs
#align uniform_on_fun.uniform_continuous_to_fun UniformOnFun.uniformContinuous_toFun