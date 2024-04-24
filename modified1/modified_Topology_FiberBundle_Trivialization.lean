def toFun' : Z → (B × F) := e.toFun

instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩

@[ext]
lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr
#align pretrivialization.ext Pretrivialization.ext'

def setSymm : e.target → Z :=
  e.target.restrict e.toPartialEquiv.symm
#align pretrivialization.set_symm Pretrivialization.setSymm

def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
  if hb : b ∈ e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else 0
#align pretrivialization.symm Pretrivialization.symm

def toFun' : Z → (B × F) := e.toFun

/-- Natural identification as a `Pretrivialization`. -/
def toPretrivialization : Pretrivialization F proj :=
  { e with }
#align trivialization.to_pretrivialization Trivialization.toPretrivialization

def preimageHomeomorph {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))
#align trivialization.preimage_homeomorph Trivialization.preimageHomeomorph

def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)
#align trivialization.source_homeomorph_base_set_prod Trivialization.sourceHomeomorphBaseSetProd

def preimageSingletonHomeomorph {b : B} (hb : b ∈ e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
  .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb)) <|
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)
#align trivialization.preimage_singleton_homeomorph Trivialization.preimageSingletonHomeomorph

def compHomeomorph {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h) where
  toPartialHomeomorph := h.toPartialHomeomorph.trans e.toPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, (· ∘ ·)]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p ∈ e.source := by simpa using hp
    simp [hp]
#align trivialization.comp_homeomorph Trivialization.compHomeomorph

def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y
#align trivialization.symm Trivialization.symm

def transFiberHomeomorph {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj where
  toPartialHomeomorph := e.toPartialHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun
#align trivialization.trans_fiber_homeomorph Trivialization.transFiberHomeomorph

def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toPartialHomeomorph.symm (b, x)).2
#align trivialization.coord_change Trivialization.coordChange

def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.continuous_coordChange e₁ h₂ h₁
#align trivialization.coord_change_homeomorph Trivialization.coordChangeHomeomorph

def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj where
  toPartialHomeomorph :=
    ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet ∩ s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1
#align trivialization.restr_open Trivialization.restrOpen

def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet ∩ frontier s)) : Trivialization F proj where
  toPartialHomeomorph :=
    e.toPartialHomeomorph.piecewise e'.toPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet := e.open_baseSet.ite e'.open_baseSet Hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p := by
    rintro (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]
#align trivialization.piecewise Trivialization.piecewise

def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) (Heq : ∀ p, proj p = a → e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2
#align trivialization.piecewise_le_of_eq Trivialization.piecewiseLeOfEq

def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <| by
    rintro p rfl
    ext1
    · simp [e.coe_fst', e'.coe_fst', *]
    · simp [coordChange_apply_snd, *]
#align trivialization.piecewise_le Trivialization.piecewiseLe

def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj where
  toPartialHomeomorph :=
    e.toPartialHomeomorph.disjointUnion e'.toPartialHomeomorph
      (by
        rw [e.source_eq, e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet ∪ e'.baseSet
  open_baseSet := IsOpen.union e.open_baseSet e'.open_baseSet
  source_eq := congr_arg₂ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_toFun := by
    rintro p (hp | hp')
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_not_mem, e'.coe_fst hp']
      simp only [source_eq] at hp' ⊢
      exact fun h => H.le_bot ⟨h, hp'⟩
#align trivialization.disjoint_union Trivialization.disjointUnion

structure extending partial homeomorphisms, defining a local
  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `Pretrivialization F proj` : trivialization as a partial equivalence, mainly used when the
  topology on the total space has not yet been defined.

### Operations on bundles

structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR leanprover-community/mathlib#17359, we have changed this to a single structure

structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.
-/

open TopologicalSpace Filter Set Bundle Function

open scoped Topology Classical Bundle

variable {ι : Type*} {B : Type*} {F : Type*} {E : B → Type*}
variable (F) {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `Trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`Pretrivialization F proj` to a `Trivialization F proj`. -/
structure Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p
#align pretrivialization Pretrivialization

structure extending partial homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a partial homeomorphism between `Z` and `B × F` defined between
two sets of the form `proj ⁻¹' baseSet` and `baseSet × F`, acting trivially on the first coordinate.
-/
-- Porting note (#5171): was @[nolint has_nonempty_instance]

structure Trivialization (proj : Z → B) extends PartialHomeomorph Z (B × F) where
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toPartialHomeomorph p).1 = proj p
#align trivialization Trivialization