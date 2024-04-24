def mfld_cfg : Simps.Config where
  attrs := [`mfld_simps]
  fullyApplied := false
#align mfld_cfg mfld_cfg

def symm : PartialEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'
#align local_equiv.symm PartialEquiv.symm

def Simps.symm_apply (e : PartialEquiv α β) : β → α :=
  e.symm
#align local_equiv.simps.symm_apply PartialEquiv.Simps.symm_apply

def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' x hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `PartialEquiv` to an `Equiv`. -/
@[simps! (config := mfld_cfg)]
def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
  e.toPartialEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]
#align equiv.to_local_equiv Equiv.toPartialEquiv

def copy (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    PartialEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv
#align local_equiv.copy PartialEquiv.copy

def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.eq <| e.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.eq <| e.right_inv hy
#align local_equiv.to_equiv PartialEquiv.toEquiv

def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_equiv.is_image PartialEquiv.IsImage

def restr (h : e.IsImage s t) : PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono (inter_subset_left _ _)
  right_inv' := e.rightInvOn.mono (inter_subset_left _ _)
#align local_equiv.is_image.restr PartialEquiv.IsImage.restr

def restr (s : Set α) : PartialEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr
#align local_equiv.restr PartialEquiv.restr

def refl (α : Type*) : PartialEquiv α α :=
  (Equiv.refl α).toPartialEquiv
#align local_equiv.refl PartialEquiv.refl

def ofSet (s : Set α) : PartialEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl
#align local_equiv.of_set PartialEquiv.ofSet

def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]
#align local_equiv.trans' PartialEquiv.trans'

def trans : PartialEquiv α γ :=
  PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)
#align local_equiv.trans PartialEquiv.trans

def EqOnSource (e e' : PartialEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'
#align local_equiv.eq_on_source PartialEquiv.EqOnSource

def prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp   := by simp_all
  right_inv' p hp  := by simp_all
#align local_equiv.prod PartialEquiv.prod

def piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    PartialEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm
#align local_equiv.piecewise PartialEquiv.piecewise

def disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : PartialEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)
#align local_equiv.disjoint_union PartialEquiv.disjointUnion

def pi (ei : ∀ i, PartialEquiv (αi i) (βi i)) : PartialEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun f i := ei i (f i)
  invFun f i := (ei i).symm (f i)
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)
#align local_equiv.pi PartialEquiv.pi

def BijOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : PartialEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2
#align set.bij_on.to_local_equiv Set.BijOn.toPartialEquiv

def InjOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    PartialEquiv α β :=
  hf.bijOn_image.toPartialEquiv f s (f '' s)
#align set.inj_on.to_local_equiv Set.InjOn.toPartialEquiv

def transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ :=
  (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)
#align equiv.trans_local_equiv Equiv.transPartialEquiv

def transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ :=
  (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)
#align local_equiv.trans_equiv PartialEquiv.transEquiv

structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x
#align local_equiv PartialEquiv