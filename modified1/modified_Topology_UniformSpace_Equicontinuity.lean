def EquicontinuousAt (F : ι → X → α) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U
#align equicontinuous_at EquicontinuousAt

def EquicontinuousWithinAt (F : ι → X → α) (S : Set X) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous at a point within a subset
if the family `(↑) : ↥H → (X → α)` is equicontinuous at that point within that same subset. -/
protected abbrev Set.EquicontinuousWithinAt (H : Set <| X → α) (S : Set X) (x₀ : X) : Prop :=
  EquicontinuousWithinAt ((↑) : H → X → α) S x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`. -/
def Equicontinuous (F : ι → X → α) : Prop :=
  ∀ x₀, EquicontinuousAt F x₀
#align equicontinuous Equicontinuous

def EquicontinuousOn (F : ι → X → α) (S : Set X) : Prop :=
  ∀ x₀ ∈ S, EquicontinuousWithinAt F S x₀

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous on a subset if the family
`(↑) : ↥H → (X → α)` is equicontinuous on that subset. -/
protected abbrev Set.EquicontinuousOn (H : Set <| X → α) (S : Set X) : Prop :=
  EquicontinuousOn ((↑) : H → X → α) S

/-- A family `F : ι → β → α` of functions between uniform spaces is *uniformly equicontinuous* if,
for all entourages `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, whenever `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i y`. -/
def UniformEquicontinuous (F : ι → β → α) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U
#align uniform_equicontinuous UniformEquicontinuous

def UniformEquicontinuousOn (F : ι → β → α) (S : Set β) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous on a subset if the
family `(↑) : ↥H → (X → α)` is uniformly equicontinuous on that subset. -/
protected abbrev Set.UniformEquicontinuousOn (H : Set <| β → α) (S : Set β) : Prop :=
  UniformEquicontinuousOn ((↑) : H → β → α) S

lemma EquicontinuousAt.equicontinuousWithinAt {F : ι → X → α} {x₀ : X} (H : EquicontinuousAt F x₀)
    (S : Set X) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left

lemma EquicontinuousWithinAt.mono {F : ι → X → α} {x₀ : X} {S T : Set X}
    (H : EquicontinuousWithinAt F T x₀) (hST : S ⊆ T) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono <| nhdsWithin_mono x₀ hST

@[simp] lemma equicontinuousWithinAt_univ (F : ι → X → α) (x₀ : X) :
    EquicontinuousWithinAt F univ x₀ ↔ EquicontinuousAt F x₀ := by
  rw [EquicontinuousWithinAt, EquicontinuousAt, nhdsWithin_univ]

lemma equicontinuousAt_restrict_iff (F : ι → X → α) {S : Set X} (x₀ : S) :
    EquicontinuousAt (S.restrict ∘ F) x₀ ↔ EquicontinuousWithinAt F S x₀ := by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]

lemma Equicontinuous.equicontinuousOn {F : ι → X → α} (H : Equicontinuous F)
    (S : Set X) : EquicontinuousOn F S :=
  fun x _ ↦ (H x).equicontinuousWithinAt S

lemma EquicontinuousOn.mono {F : ι → X → α} {S T : Set X}
    (H : EquicontinuousOn F T) (hST : S ⊆ T) : EquicontinuousOn F S :=
  fun x hx ↦ (H x (hST hx)).mono hST

lemma equicontinuousOn_univ (F : ι → X → α) :
    EquicontinuousOn F univ ↔ Equicontinuous F := by
  simp [EquicontinuousOn, Equicontinuous]

lemma equicontinuous_restrict_iff (F : ι → X → α) {S : Set X} :
    Equicontinuous (S.restrict ∘ F) ↔ EquicontinuousOn F S := by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]

lemma UniformEquicontinuous.uniformEquicontinuousOn {F : ι → β → α} (H : UniformEquicontinuous F)
    (S : Set β) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left

lemma UniformEquicontinuousOn.mono {F : ι → β → α} {S T : Set β}
    (H : UniformEquicontinuousOn F T) (hST : S ⊆ T) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono <| inf_le_inf_left _ <| principal_mono.mpr <| prod_mono hST hST

lemma uniformEquicontinuousOn_univ (F : ι → β → α) :
    UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F := by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]

lemma uniformEquicontinuous_restrict_iff (F : ι → β → α) {S : Set β} :
    UniformEquicontinuous (S.restrict ∘ F) ↔ UniformEquicontinuousOn F S := by
  rw [UniformEquicontinuous, UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prod_map, ← map_comap]

/-!
### Empty index type

structure of uniform convergence*.
This is very useful for developping the equicontinuity API, but it should not be used directly
for other purposes. -/
theorem uniformEquicontinuous_iff_uniformContinuous {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β → ι →ᵤ α) := by
  rw [UniformContinuous, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl
#align uniform_equicontinuous_iff_uniform_continuous uniformEquicontinuous_iff_uniformContinuous

structure of uniform convergence*. This is very useful
for developping the equicontinuity API, but it should not be used directly for other purposes. -/
theorem uniformEquicontinuousOn_iff_uniformContinuousOn {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (ofFun ∘ Function.swap F : β → ι →ᵤ α) S := by
  rw [UniformContinuousOn, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

theorem equicontinuousWithinAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} {x₀ : X} : EquicontinuousWithinAt (uα :=  ⨅ k, u k) F S x₀ ↔
      ∀ k, EquicontinuousWithinAt (uα :=  u k) F S x₀ := by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, nhds_iInf, tendsto_iInf]

theorem equicontinuousAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {x₀ : X} :
    EquicontinuousAt (uα := ⨅ k, u k) F x₀ ↔ ∀ k, EquicontinuousAt (uα := u k) F x₀ := by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]

theorem equicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'} :
    Equicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, Equicontinuous (uα := u k) F := by
  simp_rw [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, continuous_iInf_rng]

theorem equicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} :
    EquicontinuousOn (uα := ⨅ k, u k) F S ↔ ∀ k, EquicontinuousOn (uα := u k) F S := by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_swap _ κ]

theorem uniformEquicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'} :
    UniformEquicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, UniformEquicontinuous (uα := u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq, uniformContinuous_iInf_rng]

theorem uniformEquicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'}
    {S : Set β} : UniformEquicontinuousOn (uα := ⨅ k, u k) F S ↔
      ∀ k, UniformEquicontinuousOn (uα := u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq, iInf_uniformity, tendsto_iInf]

theorem equicontinuousWithinAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {x₀ : X'} {k : κ} (hk : EquicontinuousWithinAt (tX := t k) F S x₀) :
    EquicontinuousWithinAt (tX := ⨅ k, t k) F S x₀ := by
  simp [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k

theorem equicontinuousAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX := t k) F x₀) :
    EquicontinuousAt (tX := ⨅ k, t k) F x₀ := by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk

theorem equicontinuous_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {k : κ} (hk : Equicontinuous (tX := t k) F) :
    Equicontinuous (tX := ⨅ k, t k) F :=
  fun x ↦ equicontinuousAt_iInf_dom (hk x)

theorem equicontinuousOn_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {k : κ} (hk : EquicontinuousOn (tX := t k) F S) :
    EquicontinuousOn (tX := ⨅ k, t k) F S :=
  fun x hx ↦ equicontinuousWithinAt_iInf_dom (hk x hx)

theorem uniformEquicontinuous_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {k : κ} (hk : UniformEquicontinuous (uβ := u k) F) :
    UniformEquicontinuous (uβ := ⨅ k, u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk

theorem uniformEquicontinuousOn_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {S : Set β'} {k : κ} (hk : UniformEquicontinuousOn (uβ := u k) F S) :
    UniformEquicontinuousOn (uβ := ⨅ k, u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k

theorem Filter.HasBasis.equicontinuousAt_iff_left {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl
#align filter.has_basis.equicontinuous_at_iff_left Filter.HasBasis.equicontinuousAt_iff_left