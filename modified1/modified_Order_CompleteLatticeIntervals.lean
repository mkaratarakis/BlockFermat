def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Sup subsetSupSet

def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
      then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
      else default :=
  rfl
#align subset_Sup_def subset_sSup_def

def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Inf subsetInfSet

def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
      then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩ else
      default :=
  rfl
#align subset_Inf_def subset_sInf_def

def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    le_csSup := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s ⟨c, hct⟩ h_bdd (h_Sup ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe _).le_csSup_image hct h_bdd
    csSup_le := by
      rintro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s ht ⟨B, hB⟩ (h_Sup ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).csSup_image_le ht hB
    le_csInf := by
      intro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s ht ⟨B, hB⟩ (h_Inf ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).le_csInf_image ht hB
    csInf_le := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s ⟨c, hct⟩ h_bdd (h_Inf ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe s).csInf_image_le hct h_bdd
    csSup_of_not_bddAbove := fun t ht ↦ by simp [ht]
    csInf_of_not_bddBelow := fun t ht ↦ by simp [ht] }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

structure on a nonempty subset `s` of a preorder with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Sup subsetSupSet

structure on a nonempty subset `s` of a preorder with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Inf subsetInfSet