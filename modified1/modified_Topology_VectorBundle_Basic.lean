def symmₗ (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b := by
  refine' IsLinearMap.mk' (e.symm b) _
  by_cases hb : b ∈ e.baseSet
  · exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v ↦
      congr_arg Prod.snd <| e.apply_mk_symm hb v).isLinear
  · rw [e.coe_symm_of_not_mem hb]
    exact (0 : F →ₗ[R] E b).isLinear
#align pretrivialization.symmₗ Pretrivialization.symmₗ

def linearEquivAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F where
  toFun y := (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v
#align pretrivialization.linear_equiv_at Pretrivialization.linearEquivAt

def linearMapAt (e : Pretrivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  if hb : b ∈ e.baseSet then e.linearEquivAt R b hb else 0
#align pretrivialization.linear_map_at Pretrivialization.linearMapAt

def linearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt R b hb
#align trivialization.linear_equiv_at Trivialization.linearEquivAt

def symmₗ (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →ₗ[R] E b :=
  e.toPretrivialization.symmₗ R b
#align trivialization.symmₗ Trivialization.symmₗ

def linearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →ₗ[R] F :=
  e.toPretrivialization.linearMapAt R b
#align trivialization.linear_map_at Trivialization.linearMapAt

def coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B) :
    F ≃L[R] F :=
  { toLinearEquiv := if hb : b ∈ e.baseSet ∩ e'.baseSet
      then (e.linearEquivAt R b (hb.1 : _)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
    continuous_toFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine' (e'.continuousOn.comp_continuous _ _).snd
        · exact e.continuousOn_symm.comp_continuous (Continuous.Prod.mk b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        · exact fun y => e'.mem_source.mpr hb.2
      · rw [dif_neg hb]
        exact continuous_id
    continuous_invFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dif_pos hb]
        refine' (e.continuousOn.comp_continuous _ _).snd
        exact e'.continuousOn_symm.comp_continuous (Continuous.Prod.mk b) fun y =>
          mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
      · rw [dif_neg hb]
        exact continuous_id }
set_option linter.uppercaseLean3 false in
#align trivialization.coord_changeL Trivialization.coordChangeL

def zeroSection [∀ x, Zero (E x)] : B → TotalSpace F E := (⟨·, 0⟩)
#align bundle.zero_section Bundle.zeroSection

def continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : E b →L[R] F :=
  { e.linearMapAt R b with
    toFun := e.linearMapAt R b -- given explicitly to help `simps`
    cont := by
      dsimp
      rw [e.coe_linearMapAt b]
      refine' continuous_if_const _ (fun hb => _) fun _ => continuous_zero
      exact (e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_inducing F E b).continuous
        fun x => e.mem_source.mpr hb).snd }
#align trivialization.continuous_linear_map_at Trivialization.continuousLinearMapAt

def symmL (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →L[R] E b :=
  { e.symmₗ R b with
    toFun := e.symm b -- given explicitly to help `simps`
    cont := by
      by_cases hb : b ∈ e.baseSet
      · rw [(FiberBundle.totalSpaceMk_inducing F E b).continuous_iff]
        exact e.continuousOn_symm.comp_continuous (continuous_const.prod_mk continuous_id) fun x ↦
          mk_mem_prod hb (mem_univ x)
      · refine' continuous_zero.congr fun x => (e.symm_apply_of_not_mem hb x).symm }
set_option linter.uppercaseLean3 false in
#align trivialization.symmL Trivialization.symmL

def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) : E b ≃L[R] F :=
  { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_inducing F E b).continuous fun _ => e.mem_source.mpr hb).snd
    continuous_invFun := (e.symmL R b).continuous }
#align trivialization.continuous_linear_equiv_at Trivialization.continuousLinearEquivAt

def trivialVectorBundleCore (ι : Type*) [Inhabited ι] : VectorBundleCore R B F ι where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange _ _ _ := ContinuousLinearMap.id R F
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const
#align trivial_vector_bundle_core trivialVectorBundleCore

def toFiberBundleCore : FiberBundleCore ι B F :=
  { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).prod_map continuousOn_id) }
#align vector_bundle_core.to_fiber_bundle_core VectorBundleCore.toFiberBundleCore

def Index := ι
#align vector_bundle_core.index VectorBundleCore.Index

def Base := B
#align vector_bundle_core.base VectorBundleCore.Base

def Fiber : B → Type _ :=
  Z.toFiberBundleCore.Fiber
#align vector_bundle_core.fiber VectorBundleCore.Fiber

def proj : TotalSpace F Z.Fiber → B :=
  TotalSpace.proj
#align vector_bundle_core.proj VectorBundleCore.proj

def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber
#align vector_bundle_core.total_space VectorBundleCore.TotalSpace

def trivChange (i j : ι) : PartialHomeomorph (B × F) (B × F) :=
  Z.toFiberBundleCore.trivChange i j
#align vector_bundle_core.triv_change VectorBundleCore.trivChange

def localTriv (i : ι) : Trivialization F (π F Z.Fiber) :=
  Z.toFiberBundleCore.localTriv i
#align vector_bundle_core.local_triv VectorBundleCore.localTriv

def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
#align vector_bundle_core.local_triv_at VectorBundleCore.localTrivAt

def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
#align vector_bundle_core.local_triv_at_def VectorBundleCore.localTrivAt_def

def coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[R] F :=
  Classical.choose (a.exists_coordChange e he e' he') b
#align vector_prebundle.coord_change VectorPrebundle.coordChange

def toFiberPrebundle (a : VectorPrebundle R F E) : FiberPrebundle F E :=
  { a with
    continuous_trivChange := fun e he e' he' ↦ by
      have : ContinuousOn (fun x : B × F ↦ a.coordChange he' he x.1 x.2)
          ((e'.baseSet ∩ e.baseSet) ×ˢ univ) :=
        isBoundedBilinearMap_apply.continuous.comp_continuousOn
          ((a.continuousOn_coordChange he' he).prod_map continuousOn_id)
      rw [e.target_inter_preimage_symm_source_eq e', inter_comm]
      refine' (continuousOn_fst.prod this).congr _
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp only [Function.comp_def, Prod.map]
      rw [a.mk_coordChange _ _ hb, e'.mk_symm hb.1] }
#align vector_prebundle.to_fiber_prebundle VectorPrebundle.toFiberPrebundle

def totalSpaceTopology (a : VectorPrebundle R F E) : TopologicalSpace (TotalSpace F E) :=
  a.toFiberPrebundle.totalSpaceTopology
#align vector_prebundle.total_space_topology VectorPrebundle.totalSpaceTopology

def trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he
#align vector_prebundle.trivialization_of_mem_pretrivialization_atlas VectorPrebundle.trivializationOfMemPretrivializationAtlas

def toFiberBundle : @FiberBundle B F _ _ _ a.totalSpaceTopology _ :=
  a.toFiberPrebundle.toFiberBundle
#align vector_prebundle.to_fiber_bundle VectorPrebundle.toFiberBundle

def inCoordinates (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y) : F →SL[σ] F' :=
  ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp <|
    ϕ.comp <| (trivializationAt F E x₀).symmL 𝕜₁ x
#align continuous_linear_map.in_coordinates ContinuousLinearMap.inCoordinates

structure on `Bundle.TotalSpace F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
from `B` into `F →L[R] F` is continuous on `e.baseSet ∩ e'.baseSet` with respect to the operator
norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `VectorBundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

structure with fiber `F` (denoted with
`VectorBundle R F E`) if around every point there is a fiber bundle trivialization which is linear
in the fibers. -/
class VectorBundle : Prop where
  trivialization_linear' : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.IsLinear R
  continuousOn_coordChange' :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
        (e.baseSet ∩ e'.baseSet)
#align vector_bundle VectorBundle

structure registering how
trivialization changes act on fibers. -/
structure VectorBundleCore (ι : Type*) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F →L[R] F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j, ContinuousOn (coordChange i j) (baseSet i ∩ baseSet j)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v
#align vector_bundle_core VectorBundleCore

structure on the total space of a vector bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  Z.toFiberBundleCore.toTopologicalSpace
#align vector_bundle_core.to_topological_space VectorBundleCore.toTopologicalSpace

structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the partial equivalences are also partial homeomorphisms and hence vector bundle
trivializations. The topology on the fibers is induced from the one on the total space.

The field `exists_coordChange` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivializationAtlas`).
This makes it inconvenient to explicitly define a `coordChange` function when constructing a
`VectorPrebundle`. -/
-- Porting note(#5171): was @[nolint has_nonempty_instance]

structure VectorPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivialization_linear' : ∀ e, e ∈ pretrivializationAtlas → e.IsLinear R
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  exists_coordChange : ∀ᵉ (e ∈ pretrivializationAtlas) (e' ∈ pretrivializationAtlas),
    ∃ f : B → F →L[R] F, ContinuousOn f (e.baseSet ∩ e'.baseSet) ∧
      ∀ᵉ (b ∈ e.baseSet ∩ e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
  totalSpaceMk_inducing : ∀ b : B, Inducing (pretrivializationAt b ∘ .mk b)
#align vector_prebundle VectorPrebundle

structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`VectorPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
theorem toVectorBundle : @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_trivializationOfMemPretrivializationAtlas
    continuousOn_coordChange' := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.continuousOn_coordChange he he').congr fun b hb ↦ ?_
      ext v
      -- Porting note: help `rw` find instances
      haveI h₁ := a.linear_trivializationOfMemPretrivializationAtlas he
      haveI h₂ := a.linear_trivializationOfMemPretrivializationAtlas he'
      rw [trivializationOfMemPretrivializationAtlas] at h₁ h₂
      rw [a.coordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }
#align vector_prebundle.to_vector_bundle VectorPrebundle.toVectorBundle