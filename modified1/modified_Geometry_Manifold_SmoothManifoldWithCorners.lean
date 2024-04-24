def modelWithCornersSelf (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E where
  toPartialEquiv := PartialEquiv.refl E
  source_eq := rfl
  unique_diff' := uniqueDiffOn_univ
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
#align model_with_corners_self modelWithCornersSelf

def toFun' (e : ModelWithCorners 𝕜 E H) : H → E := e.toFun

instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H → E := ⟨toFun'⟩

/-- The inverse to a model with corners, only registered as a `PartialEquiv`. -/
protected def symm : PartialEquiv E H :=
  I.toPartialEquiv.symm
#align model_with_corners.symm ModelWithCorners.symm

def Simps.apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I
#align model_with_corners.simps.apply ModelWithCorners.Simps.apply

def Simps.symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm
#align model_with_corners.simps.symm_apply ModelWithCorners.Simps.symm_apply

def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [setOf_true, mfld_simps]
    unique_diff' := I.unique_diff'.prod I'.unique_diff'
    continuous_toFun := I.continuous_toFun.prod_map I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prod_map I'.continuous_invFun }
#align model_with_corners.prod ModelWithCorners.prod

def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  unique_diff' := UniqueDiffOn.pi ι E _ _ fun i _ => (I i).unique_diff'
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)
#align model_with_corners.pi ModelWithCorners.pi

def ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.prod 𝓘(𝕜, E)
#align model_with_corners.tangent ModelWithCorners.tangent

def ModelWithCorners.toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where
  __ := I
  left_inv := I.left_inv
  right_inv _ := I.right_inv <| I.range_eq_univ.symm ▸ mem_univ _

/-- The trivial model with corners has no boundary -/
instance modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩
#align model_with_corners_self_boundaryless modelWithCornersSelf_boundaryless

def contDiffPregroupoid : Pregroupoid H where
  property f s := ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ ↦ ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, _⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := by
    apply ContDiffOn.congr contDiff_id.contDiffOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

/-- Given a model with corners `(E, H)`, we define the groupoid of invertible `C^n` transformations
  of `H` as the invertible maps that are `C^n` when read in `E` through `I`. -/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (contDiffPregroupoid n I)
#align cont_diff_groupoid contDiffGroupoid

def analyticGroupoid : StructureGroupoid H :=
  (contDiffGroupoid ∞ I) ⊓ Pregroupoid.groupoid
    { property := fun f s => AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
        (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
      comp := fun {f g u v} hf hg _ _ _ => by
        simp only [] at hf hg ⊢
        have comp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
        apply And.intro
        · simp only [comp, preimage_inter]
          refine hg.left.comp (hf.left.mono ?_) ?_
          · simp only [subset_inter_iff, inter_subset_right]
            rw [inter_assoc]
            simp
          · intro x hx
            apply And.intro
            · rw [mem_preimage, comp_apply, I.left_inv]
              exact hx.left.right
            · apply hf.right
              rw [mem_image]
              exact ⟨x, ⟨⟨hx.left.left, hx.right⟩, rfl⟩⟩
        · simp only [comp]
          rw [image_comp]
          intro x hx
          rw [mem_image] at hx
          rcases hx with ⟨x', hx'⟩
          refine hg.right ⟨x', And.intro ?_ hx'.right⟩
          apply And.intro
          · have hx'1 : x' ∈ ((v.preimage f).preimage (I.symm)).image (I ∘ f ∘ I.symm) := by
              refine image_subset (I ∘ f ∘ I.symm) ?_ hx'.left
              rw [preimage_inter]
              refine Subset.trans ?_ (inter_subset_right (u.preimage I.symm)
                ((v.preimage f).preimage I.symm))
              apply inter_subset_left
            rcases hx'1 with ⟨x'', hx''⟩
            rw [hx''.right.symm]
            simp only [comp_apply, mem_preimage, I.left_inv]
            exact hx''.left
          · rw [mem_image] at hx'
            rcases hx'.left with ⟨x'', hx''⟩
            exact hf.right ⟨x'', ⟨⟨hx''.left.left.left, hx''.left.right⟩, hx''.right⟩⟩
      id_mem := by
        apply And.intro
        · simp only [preimage_univ, univ_inter]
          exact AnalyticOn.congr isOpen_interior
            (f := (1 : E →L[𝕜] E)) (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
            (fun z hz => (I.right_inv (interior_subset hz)).symm)
        · intro x hx
          simp only [id_comp, comp_apply, preimage_univ, univ_inter, mem_image] at hx
          rcases hx with ⟨y, hy⟩
          rw [← hy.right, I.right_inv (interior_subset hy.left)]
          exact hy.left
      locality := fun {f u} _ h => by
        simp only [] at h
        simp only [AnalyticOn]
        apply And.intro
        · intro x hx
          rcases h (I.symm x) (mem_preimage.mp hx.left) with ⟨v, hv⟩
          exact hv.right.right.left x ⟨mem_preimage.mpr ⟨hx.left, hv.right.left⟩, hx.right⟩
        · apply mapsTo'.mp
          simp only [MapsTo]
          intro x hx
          rcases h (I.symm x) hx.left with ⟨v, hv⟩
          apply hv.right.right.right
          rw [mem_image]
          have hx' := And.intro hx (mem_preimage.mpr hv.right.left)
          rw [← mem_inter_iff, inter_comm, ← inter_assoc, ← preimage_inter, inter_comm v u] at hx'
          exact ⟨x, ⟨hx', rfl⟩⟩
      congr := fun {f g u} hu fg hf => by
        simp only [] at hf ⊢
        apply And.intro
        · refine AnalyticOn.congr (IsOpen.inter (hu.preimage I.continuous_symm) isOpen_interior)
            hf.left ?_
          intro z hz
          simp only [comp_apply]
          rw [fg (I.symm z) hz.left]
        · intro x hx
          apply hf.right
          rw [mem_image] at hx ⊢
          rcases hx with ⟨y, hy⟩
          refine ⟨y, ⟨hy.left, ?_⟩⟩
          rw [comp_apply, comp_apply, fg (I.symm y) hy.left.left] at hy
          exact hy.right }

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid]
  refine And.intro (ofSet_mem_contDiffGroupoid ∞ I hs) ?_
  apply mem_groupoid_of_pregroupoid.mpr
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
      (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ I.symm) ⊆ interior (range I) by
    simp only [PartialHomeomorph.ofSet_apply, id_comp, PartialHomeomorph.ofSet_toPartialEquiv,
      PartialEquiv.ofSet_source, h, comp_apply, mem_range, image_subset_iff, true_and,
      PartialHomeomorph.ofSet_symm, PartialEquiv.ofSet_target, and_self]
    intro x hx
    refine mem_preimage.mpr ?_
    rw [← I.right_inv (interior_subset hx.right)] at hx
    exact hx.right
  apply And.intro
  · have : AnalyticOn 𝕜 (1 : E →L[𝕜] E) (univ : Set E) := (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
    exact (this.mono (subset_univ (s.preimage (I.symm) ∩ interior (range I)))).congr
      ((hs.preimage I.continuous_symm).inter isOpen_interior)
      fun z hz => (I.right_inv (interior_subset hz.right)).symm
  · intro x hx
    simp only [comp_apply, mem_image] at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy.right, I.right_inv (interior_subset hy.left.right)]
    exact hy.left.right

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true, contDiffPregroupoid] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

end analyticGroupoid

section SmoothManifoldWithCorners

/-! ### Smooth manifolds with corners -/

def maximalAtlas :=
  (contDiffGroupoid ∞ I).maximalAtlas M
#align smooth_manifold_with_corners.maximal_atlas SmoothManifoldWithCorners.maximalAtlas

def extend : PartialEquiv M E :=
  f.toPartialEquiv ≫ I.toPartialEquiv
#align local_homeomorph.extend PartialHomeomorph.extend

def extChartAt (x : M) : PartialEquiv M E :=
  (chartAt H x).extend I
#align ext_chart_at extChartAt

def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
#align written_in_ext_chart_at writtenInExtChartAt

structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : ℕ∞`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

Some texts assume manifolds to be Hausdorff and secound countable. We (in mathlib) assume neither,
but add these assumptions later as needed. (Quite a few results still do not require them.)

## Main definitions

structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `modelWithCornersSelf 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `contDiffGroupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of partial homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `SmoothManifoldWithCorners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `HasGroupoid M (contDiffGroupoid ∞ I)`.
* `extChartAt I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as partial homeomorphisms, but
  we register them as `PartialEquiv`s.
  `extChartAt I x` is the canonical such partial equiv around `x`.

As specific examples of models with corners, we define (in `Geometry.Manifold.Instances.Real`)
* `modelWithCornersSelf ℝ (EuclideanSpace (Fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `Manifold`)
* `ModelWithCorners ℝ (EuclideanSpace (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `Manifold`)
* `ModelWithCorners ℝ (EuclideanSpace (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace (Fin n)) M]
   [SmoothManifoldWithCorners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(EuclideanSpace (Fin n)) × (EuclideanSpace (Fin n))` and not on `EuclideanSpace (Fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(EuclideanSpace (Fin n)) × (EuclideanSpace (Fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]`

Here, `I.Boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `modelWithCornersSelf`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `modelWithCornersSelf ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(fun p : E × F ↦ (p.1, p.2))` is not defeq to the identity).
So, it is important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[ext] -- Porting note(#5171): was nolint has_nonempty_instance

structure ModelWithCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] extends
    PartialEquiv H E where
  source_eq : source = univ
  unique_diff' : UniqueDiffOn 𝕜 toPartialEquiv.target
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity
#align model_with_corners ModelWithCorners

structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `ModelProd H H'`
vs `H × H'`. -/
@[simps (config := .lemmasOnly)]
def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [setOf_true, mfld_simps]
    unique_diff' := I.unique_diff'.prod I'.unique_diff'
    continuous_toFun := I.continuous_toFun.prod_map I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prod_map I'.continuous_invFun }
#align model_with_corners.prod ModelWithCorners.prod

structure groupoid, avoiding the need to specify the groupoid
`contDiffGroupoid ∞ I` explicitly. -/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximalAtlas :=
  (contDiffGroupoid ∞ I).maximalAtlas M
#align smooth_manifold_with_corners.maximal_atlas SmoothManifoldWithCorners.maximalAtlas

structure on a vector space, the extended charts are just the
identity. -/
theorem extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E := by
  simp only [mfld_simps]
#align ext_chart_at_model_space_eq_id extChartAt_model_space_eq_id