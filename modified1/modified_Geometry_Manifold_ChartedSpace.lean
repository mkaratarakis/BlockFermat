def idGroupoid (H : Type u) [TopologicalSpace H] : StructureGroupoid H where
  members := {PartialHomeomorph.refl H} ∪ { e : PartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    cases' he with he he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ e' ∈ { e : PartialHomeomorph H H | e.source = ∅ } := eq_bot_iff.2 this
      exact (mem_union _ _ _).2 (Or.inr this)
  symm' e he := by
    cases' (mem_union _ _ _).1 he with E E
    · simp [mem_singleton_iff.mp E]
    · right
      simpa only [e.toPartialEquiv.image_source_eq_target.symm, mfld_simps] using E
  id_mem' := mem_union_left _ rfl
  locality' e he := by
    rcases e.source.eq_empty_or_nonempty with h | h
    · right
      exact h
    · left
      rcases h with ⟨x, hx⟩
      rcases he x hx with ⟨s, open_s, xs, hs⟩
      have x's : x ∈ (e.restr s).source := by
        rw [restr_source, open_s.interior_eq]
        exact ⟨hx, xs⟩
      cases' hs with hs hs
      · replace hs : PartialHomeomorph.restr e s = PartialHomeomorph.refl H := by
          simpa only using hs
        have : (e.restr s).source = univ := by
          rw [hs]
          simp
        have : e.toPartialEquiv.source ∩ interior s = univ := this
        have : univ ⊆ interior s := by
          rw [← this]
          exact inter_subset_right _ _
        have : s = univ := by rwa [open_s.interior_eq, univ_subset_iff] at this
        simpa only [this, restr_univ] using hs
      · exfalso
        rw [mem_setOf_eq] at hs
        rwa [hs] at x's
  mem_of_eqOnSource' e e' he he'e := by
    cases' he with he he
    · left
      have : e = e' := by
        refine' eq_of_eqOnSource_univ (Setoid.symm he'e) _ _ <;>
          rw [Set.mem_singleton_iff.1 he] <;> rfl
      rwa [← this]
    · right
      have he : e.toPartialEquiv.source = ∅ := he
      rwa [Set.mem_setOf_eq, EqOnSource.source_eq he'e]
#align id_groupoid idGroupoid

def Pregroupoid.groupoid (PG : Pregroupoid H) : StructureGroupoid H where
  members := { e : PartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.2 he.2 e'.open_target e.open_target
      apply e'.continuousOn_invFun.isOpen_inter_preimage e'.open_target e.open_target
  symm' e he := ⟨he.2, he.1⟩
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩
  locality' e he := by
    constructor
    · refine' PG.locality e.open_source fun x xu ↦ _
      rcases he x xu with ⟨s, s_open, xs, hs⟩
      refine' ⟨s, s_open, xs, _⟩
      convert hs.1 using 1
      dsimp [PartialHomeomorph.restr]
      rw [s_open.interior_eq]
    · refine' PG.locality e.open_target fun x xu ↦ _
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩
      refine' ⟨e.target ∩ e.symm ⁻¹' s, _, ⟨xu, xs⟩, _⟩
      · exact ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target s_open
      · rw [← inter_assoc, inter_self]
        convert hs.2 using 1
        dsimp [PartialHomeomorph.restr]
        rw [s_open.interior_eq]
  mem_of_eqOnSource' e e' he ee' := by
    constructor
    · apply PG.congr e'.open_source ee'.2
      simp only [ee'.1, he.1]
    · have A := EqOnSource.symm' ee'
      apply PG.congr e'.symm.open_source A.2
      -- Porting note: was
      -- convert he.2
      -- rw [A.1]
      -- rfl
      rw [A.1, symm_toPartialEquiv, PartialEquiv.symm_source]
      exact he.2
#align pregroupoid.groupoid Pregroupoid.groupoid

def continuousPregroupoid (H : Type*) [TopologicalSpace H] : Pregroupoid H where
  property _ _ := True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial
#align continuous_pregroupoid continuousPregroupoid

def continuousGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)
#align continuous_groupoid continuousGroupoid

def idRestrGroupoid : StructureGroupoid H where
  members := { e | ∃ (s : Set H) (h : IsOpen s), e ≈ PartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s ∩ s', hs.inter hs', ?_⟩
    have := PartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [PartialHomeomorph.ofSet_trans_ofSet] at this
  symm' := by
    rintro e ⟨s, hs, hse⟩
    refine' ⟨s, hs, _⟩
    rw [← ofSet_symm]
    exact PartialHomeomorph.EqOnSource.symm' hse
  id_mem' := ⟨univ, isOpen_univ, by simp only [mfld_simps, refl]⟩
  locality' := by
    intro e h
    refine' ⟨e.source, e.open_source, by simp only [mfld_simps], _⟩
    intro x hx
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩
    have hes : x ∈ (e.restr s).source := by
      rw [e.restr_source]
      refine' ⟨hx, _⟩
      rw [hs.interior_eq]
      exact hxs
    simpa only [mfld_simps] using PartialHomeomorph.EqOnSource.eqOn hes' hes
  mem_of_eqOnSource' := by
    rintro e e' ⟨s, hs, hse⟩ hee'
    exact ⟨s, hs, Setoid.trans hee' hse⟩
#align id_restr_groupoid idRestrGroupoid

def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩
#align achart achart

def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl
#align achart_def achart_def

def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 PartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩
#align charted_space.comp ChartedSpace.comp

def ModelProd (H : Type*) (H' : Type*) :=
  H × H'
#align model_prod ModelProd

def ModelPi {ι : Type*} (H : ι → Type*) :=
  ∀ i, H i
#align model_pi ModelPi

def toTopologicalSpace : TopologicalSpace M :=
  TopologicalSpace.generateFrom <|
    ⋃ (e : PartialEquiv M H) (_ : e ∈ c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s ∩ e.source}
#align charted_space_core.to_topological_space ChartedSpaceCore.toTopologicalSpace

def partialHomeomorph (e : PartialEquiv M H) (he : e ∈ c.atlas) :
    @PartialHomeomorph M H c.toTopologicalSpace _ :=
  { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert c.open_source' he
    open_target := by convert c.open_target he
    continuousOn_toFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
      rw [inter_comm]
      apply TopologicalSpace.GenerateOpen.basic
      simp only [exists_prop, mem_iUnion, mem_singleton_iff]
      exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
    continuousOn_invFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      apply continuousOn_isOpen_of_generateFrom
      intro t ht
      simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
      rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩
      rw [ts]
      let f := e.symm.trans e'
      have : IsOpen (f ⁻¹' s ∩ f.source) := by
        simpa [f, inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuousOn_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
          e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc, ← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [f, PartialEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }
#align charted_space_core.local_homeomorph ChartedSpaceCore.partialHomeomorph

def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e ∈ c.atlas), {c.partialHomeomorph e he}
    chartAt := fun x ↦ c.partialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}
#align charted_space_core.to_charted_space ChartedSpaceCore.toChartedSpace

def StructureGroupoid.maximalAtlas : Set (PartialHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }
#align structure_groupoid.maximal_atlas StructureGroupoid.maximalAtlas

def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto
#align local_homeomorph.singleton_charted_space PartialHomeomorph.singletonChartedSpace

def singletonChartedSpace {f : α → H} (h : OpenEmbedding f) : ChartedSpace H α :=
  (h.toPartialHomeomorph f).singletonChartedSpace (toPartialHomeomorph_source _ _)
#align open_embedding.singleton_charted_space OpenEmbedding.singletonChartedSpace

def Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' ↦ by
      change PartialHomeomorph.symm c ≫ₕ PartialHomeomorph.refl M ≫ₕ c' ∈ G
      rw [PartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }
#align structomorph.refl Structomorph.refl

def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
  { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toPartialHomeomorph ≫ₕ c).symm ∈ G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }
#align structomorph.symm Structomorph.symm

def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
    Structomorph G M M'' :=
  { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine' G.locality fun x hx ↦ _
      let f₁ := e.toHomeomorph.toPartialHomeomorph
      let f₂ := e'.toHomeomorph.toPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toPartialHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source ∩ c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x ∈ s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine' ⟨s, open_s, this, _⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ ∈ G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' :=
          by simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s :=
          by simp only [EqOnSource.restr, trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ ∈ G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }
#align structomorph.trans Structomorph.trans

structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of partial homeomorphisms stable
under composition and inverse, to which the change of coordinates should belong.

## Main definitions

structure on `M` modelled on `H`, given by an atlas of
  partial homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `HasGroupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximalAtlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the partial homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `Structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `Pregroupoid H` : a subset of partial maps of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `Pregroupoid.groupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chartAt H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximalAtlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `ChartedSpaceCore.toChartedSpace`: consider a space without a topology, but endowed with a set
  of charts (which are partial equivs) for which the change of coordinates are partial homeos.
  Then one can construct a topology on the space for which the charts become partial homeos,
  defining a genuine charted space structure.

## Implementation notes

structure `ChartedSpaceCore` making it possible to construct a topology out of a set of
partial equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notations

structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`. There is a typeclass `ClosedUnderRestriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if a partial homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of structomorphisms does not have to be a structomorphism. Note that
this implies that a partial homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a partial homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`Membership` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/


/-- A structure groupoid is a set of partial homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure StructureGroupoid (H : Type u) [TopologicalSpace H] where
  members : Set (PartialHomeomorph H H)
  trans' : ∀ e e' : PartialHomeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members
  symm' : ∀ e : PartialHomeomorph H H, e ∈ members → e.symm ∈ members
  id_mem' : PartialHomeomorph.refl H ∈ members
  locality' : ∀ e : PartialHomeomorph H H,
    (∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ members) → e ∈ members
  mem_of_eqOnSource' : ∀ e e' : PartialHomeomorph H H, e ∈ members → e' ≈ e → e' ∈ members
#align structure_groupoid StructureGroupoid

structure groupoid contains the identity groupoid. -/
instance instStructureGroupoidOrderBot : OrderBot (StructureGroupoid H) where
  bot := idGroupoid H
  bot_le := by
    intro u f hf
    have hf : f ∈ {PartialHomeomorph.refl H} ∪ { e : PartialHomeomorph H H | e.source = ∅ } := hf
    simp only [singleton_union, mem_setOf_eq, mem_insert_iff] at hf
    cases' hf with hf hf
    · rw [hf]
      apply u.id_mem
    · apply u.locality
      intro x hx
      rw [hf, mem_empty_iff_false] at hx
      exact hx.elim

instance : Inhabited (StructureGroupoid H) := ⟨idGroupoid H⟩

/-- To construct a groupoid, one may consider classes of partial homeomorphisms such that
both the function and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `Pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure Pregroupoid (H : Type*) [TopologicalSpace H] where
  property : (H → H) → Set H → Prop
  comp : ∀ {f g u v}, property f u → property g v →
    IsOpen u → IsOpen v → IsOpen (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  id_mem : property id univ
  locality :
    ∀ {f u}, IsOpen u → (∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u
  congr : ∀ {f g : H → H} {u}, IsOpen u → (∀ x ∈ u, g x = f x) → property f u → property g u
#align pregroupoid Pregroupoid

structure groupoid is contained in the groupoid of all partial homeomorphisms. -/
instance instStructureGroupoidOrderTop : OrderTop (StructureGroupoid H) where
  top := continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

instance : CompleteLattice (StructureGroupoid H) :=
  { SetLike.instPartialOrder,
    completeLatticeOfInf _ (by
      refine' fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_le
    top := instStructureGroupoidOrderTop.top
    le_top := instStructureGroupoidOrderTop.le_top
    inf := (· ⊓ ·)
    le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class ClosedUnderRestriction (G : StructureGroupoid H) : Prop where
  closedUnderRestriction :
    ∀ {e : PartialHomeomorph H H}, e ∈ G → ∀ s : Set H, IsOpen s → e.restr s ∈ G
#align closed_under_restriction ClosedUnderRestriction

structure of a space modelled over itself through the identity,
the atlas members are just the identity. -/
@[simp, mfld_simps]
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : PartialHomeomorph H H} :
    e ∈ atlas H H ↔ e = PartialHomeomorph.refl H :=
  Iff.rfl
#align charted_space_self_atlas chartedSpaceSelf_atlas

structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only partial equivs, and continuity properties for their composition.
This is formalised in `ChartedSpaceCore`. -/
-- Porting note(#5171): this linter isn't ported yet.

structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  atlas : Set (PartialEquiv M H)
  chartAt : M → PartialEquiv M H
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas
  open_source : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').source
  continuousOn_toFun : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas →
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source
#align charted_space_core ChartedSpaceCore

structure with
respect to the topology constructed from the atlas. -/
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e ∈ c.atlas), {c.partialHomeomorph e he}
    chartAt := fun x ↦ c.partialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}
#align charted_space_core.to_charted_space ChartedSpaceCore.toChartedSpace

structure groupoid -/


section HasGroupoid

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid. -/
class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible : ∀ {e e' : PartialHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G
#align has_groupoid HasGroupoid

structure groupoid, to make it more easily accessible with dot
notation. -/
theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : PartialHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) : e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible he he'
#align structure_groupoid.compatible StructureGroupoid.compatible

structure on the model space is compatible with any groupoid. -/
instance hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H) :
    HasGroupoid H G where
  compatible {e e'} he he' := by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]
#align has_groupoid_model_space hasGroupoid_model_space

structure is compatible with the groupoid of all partial homeomorphisms. -/
instance hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H) := by
  refine' ⟨fun _ _ ↦ _⟩
  rw [continuousGroupoid, mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]
#align has_groupoid_continuous_groupoid hasGroupoid_continuousGroupoid

structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
def StructureGroupoid.maximalAtlas : Set (PartialHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }
#align structure_groupoid.maximal_atlas StructureGroupoid.maximalAtlas

structure groupoid. -/
theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M ⊆ G.maximalAtlas M :=
  fun _ he _ he' ↦ ⟨G.compatible he he', G.compatible he' he⟩
#align structure_groupoid.subset_maximal_atlas StructureGroupoid.subset_maximalAtlas

structure groupoid. -/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : PartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) (he' : e' ∈ G.maximalAtlas M) : e.symm ≫ₕ e' ∈ G := by
  refine' G.locality fun x hx ↦ _
  set f := chartAt (H := H) (e.symm x)
  let s := e.target ∩ e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x ∈ s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine' ⟨s, hs, xs, _⟩
  have A : e.symm ≫ₕ f ∈ G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ∈ G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)
#align structure_groupoid.compatible_of_mem_maximal_atlas StructureGroupoid.compatible_of_mem_maximalAtlas

structure groupoid is stable under equivalence. -/
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : PartialHomeomorph M H} (h : e' ≈ e)
    (he : e ∈ G.maximalAtlas M) : e' ∈ G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

variable (G)

/-- In the model space, the identity is in any maximal atlas. -/
theorem StructureGroupoid.id_mem_maximalAtlas : PartialHomeomorph.refl H ∈ G.maximalAtlas H :=
  G.subset_maximalAtlas <| by simp
#align structure_groupoid.id_mem_maximal_atlas StructureGroupoid.id_mem_maximalAtlas

structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`OpenEmbedding.singletonChartedSpace`.) -/
def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto
#align local_homeomorph.singleton_charted_space PartialHomeomorph.singletonChartedSpace

structure on `α` is `HasGroupoid G` for any structure
groupoid `G` which is closed under restrictions. -/
theorem singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G :=
  { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he',
        e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine' G.mem_of_eqOnSource _ e.symm_trans_self
      have hle : idRestrGroupoid ≤ G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }
#align local_homeomorph.singleton_has_groupoid PartialHomeomorph.singleton_hasGroupoid

structure on `α`.
See `PartialHomeomorph.singletonChartedSpace`. -/
def singletonChartedSpace {f : α → H} (h : OpenEmbedding f) : ChartedSpace H α :=
  (h.toPartialHomeomorph f).singletonChartedSpace (toPartialHomeomorph_source _ _)
#align open_embedding.singleton_charted_space OpenEmbedding.singletonChartedSpace

structure Structomorph (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M'] extends Homeomorph M M' where
  mem_groupoid : ∀ c : PartialHomeomorph M H, ∀ c' : PartialHomeomorph M' H, c ∈ atlas H M →
    c' ∈ atlas H M' → c.symm ≫ₕ toHomeomorph.toPartialHomeomorph ≫ₕ c' ∈ G
#align structomorph Structomorph