def toFun' : X → Y := e.toFun

/-- Coercion of a `PartialHomeomorph` to function.
Note that a `PartialHomeomorph` is not `DFunLike`. -/
instance : CoeFun (PartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a partial homeomorphism -/
@[symm]
protected def symm : PartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  open_source := e.open_target
  open_target := e.open_source
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun
#align local_homeomorph.symm PartialHomeomorph.symm

def Simps.apply (e : PartialHomeomorph X Y) : X → Y := e
#align local_homeomorph.simps.apply PartialHomeomorph.Simps.apply

def Simps.symm_apply (e : PartialHomeomorph X Y) : Y → X := e.symm
#align local_homeomorph.simps.symm_apply PartialHomeomorph.Simps.symm_apply

def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a partial homeomorphism on the whole space -/
@[simps! (config := mfld_cfg)]
def _root_.Homeomorph.toPartialHomeomorph (e : X ≃ₜ Y) : PartialHomeomorph X Y :=
  e.toPartialHomeomorphOfImageEq univ isOpen_univ univ <| by rw [image_univ, e.surjective.range_eq]
#align homeomorph.to_local_homeomorph Homeomorph.toPartialHomeomorph

def replaceEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y) (h : e.toPartialEquiv = e') :
    PartialHomeomorph X Y where
  toPartialEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun
#align local_homeomorph.replace_equiv PartialHomeomorph.replaceEquiv

def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image PartialHomeomorph.IsImage

def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : PartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono (inter_subset_left _ _)
  continuousOn_invFun := e.symm.continuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr PartialHomeomorph.IsImage.restr

def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : PartialHomeomorph X Y where
  toPartialEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn
#align local_homeomorph.of_continuous_open_restrict PartialHomeomorph.ofContinuousOpenRestrict

def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open PartialHomeomorph.ofContinuousOpen

def restrOpen (s : Set X) (hs : IsOpen s) : PartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open PartialHomeomorph.restrOpen

def restr (s : Set X) : PartialHomeomorph X Y :=
  e.restrOpen (interior s) isOpen_interior
#align local_homeomorph.restr PartialHomeomorph.restr

def refl (X : Type*) [TopologicalSpace X] : PartialHomeomorph X X :=
  (Homeomorph.refl X).toPartialHomeomorph
#align local_homeomorph.refl PartialHomeomorph.refl

def ofSet (s : Set X) (hs : IsOpen s) : PartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn
#align local_homeomorph.of_set PartialHomeomorph.ofSet

def trans' (h : e.target = e'.source) : PartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo
#align local_homeomorph.trans' PartialHomeomorph.trans'

def trans : PartialHomeomorph X Z :=
  PartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans PartialHomeomorph.trans

def EqOnSource (e e' : PartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source PartialHomeomorph.EqOnSource

def prod (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    PartialHomeomorph (X × Y) (X' × Y') where
  open_source := eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prod_map eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prod_map eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv
#align local_homeomorph.prod PartialHomeomorph.prod

def pi : PartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
#align local_homeomorph.pi PartialHomeomorph.pi

def piecewise (e e' : PartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)
#align local_homeomorph.piecewise PartialHomeomorph.piecewise

def disjointUnion (e e' : PartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : PartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union PartialHomeomorph.disjointUnion

def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo'.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_subset e hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.eq <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).restrict_mapsTo h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).restrict_mapsTo h₃ }
#align local_homeomorph.homeomorph_of_image_subset_source PartialHomeomorph.homeomorphOfImageSubsetSource

def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target PartialHomeomorph.toHomeomorphSourceTarget

def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuous_iff_continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuous_iff_continuousOn_univ, h'] using e.continuousOn_symm
#align local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ PartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv

def transPartialHomeomorph (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transPartialHomeomorph

def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.injOn univ).toPartialEquiv _ _)
    h.continuous.continuousOn h.isOpenMap isOpen_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toPartialHomeomorph

def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  OpenEmbedding.toPartialHomeomorph _ s.2.openEmbedding_subtype_val
#align topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.partialHomeomorphSubtypeCoe

def transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id
#align local_homeomorph.trans_homeomorph PartialHomeomorph.transHomeomorph

def subtypeRestr : PartialHomeomorph s Y :=
  (s.partialHomeomorphSubtypeCoe hs).trans e
#align local_homeomorph.subtype_restr PartialHomeomorph.subtypeRestr

def : e.subtypeRestr hs = (s.partialHomeomorphSubtypeCoe hs).trans e :=
  rfl
#align local_homeomorph.subtype_restr_def PartialHomeomorph.subtypeRestr_def

structure PartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
  [TopologicalSpace Y] extends PartialEquiv X Y where
  open_source : IsOpen source
  open_target : IsOpen target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target
#align local_homeomorph PartialHomeomorph