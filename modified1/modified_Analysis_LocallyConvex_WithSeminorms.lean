def basisSets (p : SeminormFamily 𝕜 E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)
#align seminorm_family.basis_sets SeminormFamily.basisSets

def addGroupFilterBasis [Nonempty ι] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg
#align seminorm_family.add_group_filter_basis SeminormFamily.addGroupFilterBasis

def moduleFilterBasis : ModuleFilterBasis 𝕜 E where
  toAddGroupFilterBasis := p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right
#align seminorm_family.module_filter_basis SeminormFamily.moduleFilterBasis

def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p
#align seminorm.is_bounded Seminorm.IsBounded

def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f
#align seminorm_family.comp SeminormFamily.comp

def SeminormFamily.sigma {κ : ι → Type*} (p : (i : ι) → SeminormFamily 𝕜 E (κ i)) :
    SeminormFamily 𝕜 E ((i : ι) × κ i) :=
  fun ⟨i, k⟩ => p i k

theorem withSeminorms_iInf {κ : ι → Type*} [Nonempty ((i : ι) × κ i)] [∀ i, Nonempty (κ i)]
    {p : (i : ι) → SeminormFamily 𝕜 E (κ i)} {t : ι → TopologicalSpace E}
    [∀ i, @TopologicalAddGroup E (t i) _] (hp : ∀ i, WithSeminorms (topology := t i) (p i)) :
    WithSeminorms (topology := ⨅ i, t i) (SeminormFamily.sigma p) := by
  have : @TopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf (fun i ↦ inferInstance)
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [Countable ι]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]

/-- If the topology of a space is induced by a countable family of seminorms, then the topology
is first countable. -/
theorem WithSeminorms.first_countable (hp : WithSeminorms p) :
    FirstCountableTopology E := by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  have : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := UniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E
#align with_seminorms.first_countable WithSeminorms.first_countable

structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E] : Prop where
  topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology
#align with_seminorms WithSeminorms

structure induced by a family of seminorms is exactly the infimum of the ones
induced by each seminorm individually. We express this as a characterization of
`WithSeminorms p`. -/
theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
    [UniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    UniformAddGroup.ext_iff inferInstance (uniformAddGroup_iInf fun i => inferInstance),
    UniformSpace.toTopologicalSpace_iInf, nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup
#align seminorm_family.with_seminorms_iff_uniform_space_eq_infi SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf