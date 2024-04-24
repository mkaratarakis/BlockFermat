def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet[m] <| f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl s hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using m.measurableSet_iUnion _ hf
#align measurable_space.map MeasurableSpace.map

def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl

@[simp]
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun _ => Iff.rfl
#align measurable_space.map_id MeasurableSpace.map_id

def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun s ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩
#align measurable_space.comap MeasurableSpace.comap

def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
#align measurable_space.prod MeasurableSpace.prod

def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align measurable_equiv.refl MeasurableEquiv.refl

def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun
#align measurable_equiv.trans MeasurableEquiv.trans

def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun
  measurable_invFun := ab.measurable_toFun
#align measurable_equiv.symm MeasurableEquiv.symm

def Simps.apply (h : α ≃ᵐ β) : α → β := h
#align measurable_equiv.simps.apply MeasurableEquiv.Simps.apply

def Simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm
#align measurable_equiv.simps.symm_apply MeasurableEquiv.Simps.symm_apply

def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : HEq i₁ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h
  measurable_toFun := by
    subst h
    subst hi
    exact measurable_id
  measurable_invFun := by
    subst h
    subst hi
    exact measurable_id
#align measurable_equiv.cast MeasurableEquiv.cast

def ulift.{u, v} {α : Type u} [MeasurableSpace α] : ULift.{v, u} α ≃ᵐ α :=
  ⟨Equiv.ulift, measurable_down, measurable_up⟩

protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable
#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iff

def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := equivOfUnique α β
  measurable_toFun := Subsingleton.measurable
  measurable_invFun := Subsingleton.measurable
#align measurable_equiv.of_unique_of_unique MeasurableEquiv.ofUniqueOfUnique

def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv
  measurable_toFun :=
    (ab.measurable_toFun.comp measurable_id.fst).prod_mk
      (cd.measurable_toFun.comp measurable_id.snd)
  measurable_invFun :=
    (ab.measurable_invFun.comp measurable_id.fst).prod_mk
      (cd.measurable_invFun.comp measurable_id.snd)
#align measurable_equiv.prod_congr MeasurableEquiv.prodCongr

def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β
  measurable_toFun := measurable_id.snd.prod_mk measurable_id.fst
  measurable_invFun := measurable_id.snd.prod_mk measurable_id.fst
#align measurable_equiv.prod_comm MeasurableEquiv.prodComm

def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := measurable_fst.fst.prod_mk <| measurable_fst.snd.prod_mk measurable_snd
  measurable_invFun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd
#align measurable_equiv.prod_assoc MeasurableEquiv.prodAssoc

def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : Sum α γ ≃ᵐ Sum β δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable
#align measurable_equiv.sum_congr MeasurableEquiv.sumCongr

def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun :=
    measurable_id.subtype_val.fst.subtype_mk.prod_mk measurable_id.subtype_val.snd.subtype_mk
  measurable_invFun :=
    Measurable.subtype_mk <| measurable_id.fst.subtype_val.prod_mk measurable_id.snd.subtype_val
#align measurable_equiv.set.prod MeasurableEquiv.Set.prod

def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk
#align measurable_equiv.set.univ MeasurableEquiv.Set.univ

def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const
#align measurable_equiv.set.singleton MeasurableEquiv.Set.singleton

def Set.rangeInl : (range Sum.inl : Set (α ⊕ β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine' ⟨_, hs.inl_image, Set.ext _⟩
    rintro ⟨ab, a, rfl⟩
    simp [Set.range_inl]
  measurable_invFun := Measurable.subtype_mk measurable_inl
#align measurable_equiv.set.range_inl MeasurableEquiv.Set.rangeInl

def Set.rangeInr : (range Sum.inr : Set (Sum α β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine' ⟨_, hs.inr_image, Set.ext _⟩
    rintro ⟨ab, b, rfl⟩
    simp [Set.range_inr]
  measurable_invFun := Measurable.subtype_mk measurable_inr
#align measurable_equiv.set.range_inr MeasurableEquiv.Set.rangeInr

def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) where
  toEquiv := .sumProdDistrib α β γ
  measurable_toFun := by
    refine'
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) _ _
    · refine' (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 _
      refine' (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 _
      exact measurable_inl
    · refine' (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 _
      refine' (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 _
      exact measurable_inr
  measurable_invFun :=
    measurable_sum ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd)
#align measurable_equiv.sum_prod_distrib MeasurableEquiv.sumProdDistrib

def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm
#align measurable_equiv.prod_sum_distrib MeasurableEquiv.prodSumDistrib

def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)
#align measurable_equiv.sum_prod_sum MeasurableEquiv.sumProdSum

def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)
#align measurable_equiv.Pi_congr_right MeasurableEquiv.piCongrRight

def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a := by
  refine' { Equiv.piCongrLeft π f with .. }
  · exact measurable_piCongrLeft f
  simp only [invFun_as_coe, coe_fn_symm_mk]
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (f i)

theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! (config := .asFn)]
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h
#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTProd

def piUnique [Unique δ'] : (∀ i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_uniqueElim

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! (config := .asFn)]
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _
#align measurable_equiv.fun_unique MeasurableEquiv.funUnique

def piFinTwo (α : Fin 2 → Type*) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  measurable_toFun := Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  measurable_invFun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩
#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwo

def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α
#align measurable_equiv.fin_two_arrow MeasurableEquiv.finTwoArrow

def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j) where
  toEquiv := .piFinSuccAbove α i
  measurable_toFun := (measurable_pi_apply i).prod_mk <| measurable_pi_iff.2 fun j =>
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 <| i.forall_iff_succAbove.2
    ⟨by simp only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_same, measurable_fst],
      fun j => by simpa only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_succAbove]
        using (measurable_pi_apply _).comp measurable_snd⟩
#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAbove

def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π
  measurable_toFun := measurable_piEquivPiSubtypeProd π p
  measurable_invFun := measurable_piEquivPiSubtypeProd_symm π p
#align measurable_equiv.pi_equiv_pi_subtype_prod MeasurableEquiv.piEquivPiSubtypeProd

def sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') := by
  refine' { Equiv.sumPiEquivProdPi α with .. }
  · refine Measurable.prod ?_ ?_ <;>
      rw [measurable_pi_iff] <;> rintro i <;> apply measurable_pi_apply
  · rw [measurable_pi_iff]; rintro (i|i)
    exact measurable_pi_iff.1 measurable_fst _
    exact measurable_pi_iff.1 measurable_snd _

theorem coe_sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α := by rfl

theorem coe_sumPiEquivProdPi_symm (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

/-- The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i)`
  for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equivalence. -/
def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
    ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i :=
  letI e := Finset.union s t h
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ π (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) e

/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`. -/
def sumCompl {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    s ⊕ (sᶜ : Set α) ≃ᵐ α where
  toEquiv := .sumCompl (· ∈ s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs
#align measurable_equiv.sum_compl MeasurableEquiv.sumCompl

def ofInvolutive (f : α → α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm
  measurable_toFun := hf'
  measurable_invFun := hf'
#align measurable_equiv.of_involutive MeasurableEquiv.ofInvolutive

def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩; simp [preimage_preimage, Set.image_symm_preimage hf.injective]
    exact measurable_subtype_coe (hf.measurableSet_image' hu)
#align measurable_embedding.equiv_image MeasurableEmbedding.equivImage

def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
#align measurable_embedding.equiv_range MeasurableEmbedding.equivRange

def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ'A : Set α, MeasurableSet A ∧ F A = A by
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine'
      (MeasurableEquiv.sumCompl Ameas).symm.trans
        (MeasurableEquiv.trans _ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun h =>
    compl_subset_compl.mpr <| Set.image_subset _ <| compl_subset_compl.mpr <| Set.image_subset _ h
  let X : ℕ → Set α := fun n => F^[n] univ
  refine' ⟨iInter X, _, _⟩
  · apply MeasurableSet.iInter
    intro n
    induction' n with n ih
    · exact MeasurableSet.univ
    rw [Function.iterate_succ', Function.comp_apply]
    exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [(injOn_of_injective hf.injective _).image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
#align measurable_embedding.schroeder_bernstein MeasurableEmbedding.schroederBernstein

def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ ⋃ n, s n = univ
#align is_countably_spanning IsCountablySpanning

structure on the product of two measurable spaces. -/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
#align measurable_space.prod MeasurableSpace.prod

structure MeasurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)
#align measurable_embedding MeasurableEmbedding

structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm
#align measurable_equiv MeasurableEquiv