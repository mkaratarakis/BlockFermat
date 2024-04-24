def Index (_Z : FiberBundleCore ι B F) := ι
#align fiber_bundle_core.index FiberBundleCore.Index

def Base (_Z : FiberBundleCore ι B F) := B
#align fiber_bundle_core.base FiberBundleCore.Base

def Fiber (_ : FiberBundleCore ι B F) (_x : B) := F
#align fiber_bundle_core.fiber FiberBundleCore.Fiber

def TotalSpace := Bundle.TotalSpace F Z.Fiber
#align fiber_bundle_core.total_space FiberBundleCore.TotalSpace

def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj
#align fiber_bundle_core.proj FiberBundleCore.proj

def trivChange (i j : ι) : PartialHomeomorph (B × F) (B × F) where
  source := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp, Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true_iff, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prod (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prod (Z.continuousOn_coordChange j i)
#align fiber_bundle_core.triv_change FiberBundleCore.trivChange

def localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F) where
  source := Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true_iff, Set.mem_univ, Set.prod_mk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true_iff, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x ∈ Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, and_true_iff, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]
#align fiber_bundle_core.local_triv_as_local_equiv FiberBundleCore.localTrivAsPartialEquiv

def localTriv (i : ι) : Trivialization F Z.proj where
  baseSet := Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht ↦ ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source ∩ localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [PartialEquiv.right_inv, preimage_inter, PartialEquiv.left_inv]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i
#align fiber_bundle_core.local_triv FiberBundleCore.localTriv

def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
#align fiber_bundle_core.local_triv_at FiberBundleCore.localTrivAt

def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
#align fiber_bundle_core.local_triv_at_def FiberBundleCore.localTrivAt_def

def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (_ : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype
#align fiber_prebundle.total_space_topology FiberPrebundle.totalSpaceTopology

def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s ∩ e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u ∩ e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }
#align fiber_prebundle.trivialization_of_mem_pretrivialization_atlas FiberPrebundle.trivializationOfMemPretrivializationAtlas

def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_inducing' := fun b ↦ a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_inducing b)
    trivializationAtlas' :=
      { e | ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x ↦
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x ↦ ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }
#align fiber_prebundle.to_fiber_bundle FiberPrebundle.toFiberBundle

structure on `Bundle.TotalSpace F E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `Bundle.TotalSpace F E`, for which the projection to `B` is
a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
from `E x` to `Bundle.TotalSpace F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `FiberBundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`FiberBundleCore` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `FiberPrebundle` which allows to define a topological
fiber bundle from trivializations given as partial equivalences with minimum additional properties.

## Main definitions

structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : FiberBundleCore ι B F`. Then we define

* `Z.Fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.TotalSpace`  : the total space of `Z`, defined as `Bundle.TotalSpace F Z.Fiber` with a custom
                    topology.
* `Z.proj`        : projection from `Z.TotalSpace` to `B`. It is continuous.
* `Z.localTriv i` : for `i : ι`, bundle trivialization above the set `Z.baseSet i`, which is an
                    open set in `B`.

* `FiberPrebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are partial homeomorphisms.
* `FiberPrebundle.totalSpaceTopology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`FiberBundleCore`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
(from `F` to `F`) and the manifold derivative (from `TangentSpace I x` to `TangentSpace I' (f x)`)
are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean can not check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`TangentSpace I x`. One could fear issues as this composition goes from `TangentSpace I x` to
`TangentSpace I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `FiberBundleCore`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `FiberBundleCore`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is
`Bundle.TotalSpace F (fun b : B ↦ F)`, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `FiberBundleCore`, the indexing type will be the same as
for the initial bundle.

## Tags

structure group
-/


variable {ι B F X : Type*} [TopologicalSpace X]

open TopologicalSpace Filter Set Bundle Topology

/-! ### General definition of fiber bundles -/

structure FiberBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v
#align fiber_bundle_core FiberBundleCore

structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber) :=
  TopologicalSpace.generateFrom <| ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source ∩ Z.localTrivAsPartialEquiv i ⁻¹' s}
#align fiber_bundle_core.to_topological_space FiberBundleCore.toTopologicalSpace

structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the partial equivalences
are also partial homeomorphisms and hence local trivializations. -/
-- Porting note (#5171): was @[nolint has_nonempty_instance]

structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  continuous_trivChange : ∀ e, e ∈ pretrivializationAtlas → ∀ e', e' ∈ pretrivializationAtlas →
    ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpaceMk_inducing : ∀ b : B, Inducing (pretrivializationAt b ∘ TotalSpace.mk b)
#align fiber_prebundle FiberPrebundle

structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`FiberPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_inducing' := fun b ↦ a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_inducing b)
    trivializationAtlas' :=
      { e | ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x ↦
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x ↦ ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }
#align fiber_prebundle.to_fiber_bundle FiberPrebundle.toFiberBundle