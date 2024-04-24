def groupFilterBasisOfComm {G : Type*} [CommGroup G] (sets : Set (Set G))
    (nonempty : sets.Nonempty) (inter_sets : ∀ x y, x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
    (one : ∀ U ∈ sets, (1 : G) ∈ U) (mul : ∀ U ∈ sets, ∃ V ∈ sets, V * V ⊆ U)
    (inv : ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U) : GroupFilterBasis G :=
  { sets := sets
    nonempty := nonempty
    inter_sets := inter_sets _ _
    one' := one _
    mul' := mul _
    inv' := inv _
    conj' := fun x U U_in ↦ ⟨U, U_in, by simp only [mul_inv_cancel_comm, preimage_id']; rfl⟩ }
#align group_filter_basis_of_comm groupFilterBasisOfComm

def N (B : GroupFilterBasis G) : G → Filter G :=
  fun x ↦ map (fun y ↦ x * y) B.toFilterBasis.filter
set_option linter.uppercaseLean3 false in
#align group_filter_basis.N GroupFilterBasis.N

def topology (B : GroupFilterBasis G) : TopologicalSpace G :=
  TopologicalSpace.mkOfNhds B.N
#align group_filter_basis.topology GroupFilterBasis.topology

def topology : TopologicalSpace R :=
  B.toAddGroupFilterBasis.topology
#align ring_filter_basis.topology RingFilterBasis.topology

def topology : TopologicalSpace M :=
  B.toAddGroupFilterBasis.topology
#align module_filter_basis.topology ModuleFilterBasis.topology

def topology' {R M : Type*} [CommRing R] {_ : TopologicalSpace R} [AddCommGroup M] [Module R M]
    (B : ModuleFilterBasis R M) : TopologicalSpace M :=
  B.toAddGroupFilterBasis.topology
#align module_filter_basis.topology' ModuleFilterBasis.topology'

def ofBases {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (BR : RingFilterBasis R)
    (BM : AddGroupFilterBasis M) (smul : ∀ {U}, U ∈ BM → ∃ V ∈ BR, ∃ W ∈ BM, V • W ⊆ U)
    (smul_left : ∀ (x₀ : R) {U}, U ∈ BM → ∃ V ∈ BM, V ⊆ (fun x ↦ x₀ • x) ⁻¹' U)
    (smul_right : ∀ (m₀ : M) {U}, U ∈ BM → ∃ V ∈ BR, V ⊆ (fun x ↦ x • m₀) ⁻¹' U) :
    @ModuleFilterBasis R M _ BR.topology _ _ :=
  let _ := BR.topology
  { BM with
    smul' := by
      intro U U_in
      rcases smul U_in with ⟨V, V_in, W, W_in, H⟩
      exact ⟨V, BR.toAddGroupFilterBasis.mem_nhds_zero V_in, W, W_in, H⟩
    smul_left' := smul_left
    smul_right' := by
      intro m₀ U U_in
      rcases smul_right m₀ U_in with ⟨V, V_in, H⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) H }
#align module_filter_basis.of_bases ModuleFilterBasis.ofBases

structure
* `GroupFilterBasis.topology`: the associated topology
* `GroupFilterBasis.isTopologicalGroup`: the compatibility between the above topology
  and the group structure
* `RingFilterBasis R`: the type of filter bases that will become neighborhood of `0`
  for a topology on `R` compatible with the ring structure
* `RingFilterBasis.topology`: the associated topology
* `RingFilterBasis.isTopologicalRing`: the compatibility between the above topology
  and the ring structure

## References

structure on `G`. -/
class GroupFilterBasis (G : Type u) [Group G] extends FilterBasis G where
  one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U
  mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U
  inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U
  conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ * x * x₀⁻¹) ⁻¹' U
#align group_filter_basis GroupFilterBasis

structure on `G`. -/
class AddGroupFilterBasis (A : Type u) [AddGroup A] extends FilterBasis A where
  zero' : ∀ {U}, U ∈ sets → (0 : A) ∈ U
  add' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U
  neg' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ -x) ⁻¹' U
  conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ + x + -x₀) ⁻¹' U
#align add_group_filter_basis AddGroupFilterBasis

structure coming from a group filter basis. -/
@[to_additive "The topological space structure coming from an additive group filter basis."]
def topology (B : GroupFilterBasis G) : TopologicalSpace G :=
  TopologicalSpace.mkOfNhds B.N
#align group_filter_basis.topology GroupFilterBasis.topology

structure coming from a group filter basis then it's a
topological group. -/
@[to_additive "If a group is endowed with a topological structure coming from a group filter basis
then it's a topological group."]
instance (priority := 100) isTopologicalGroup (B : GroupFilterBasis G) :
    @TopologicalGroup G B.topology _ := by
  letI := B.topology
  have basis := B.nhds_one_hasBasis
  have basis' := basis.prod basis
  refine' TopologicalGroup.of_nhds_one _ _ _ _
  · rw [basis'.tendsto_iff basis]
    suffices ∀ U ∈ B, ∃ V W, (V ∈ B ∧ W ∈ B) ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U by simpa
    intro U U_in
    rcases mul U_in with ⟨V, V_in, hV⟩
    refine' ⟨V, V, ⟨V_in, V_in⟩, _⟩
    intro a b a_in b_in
    exact hV <| mul_mem_mul a_in b_in
  · rw [basis.tendsto_iff basis]
    intro U U_in
    simpa using inv U_in
  · intro x₀
    rw [nhds_eq, nhds_one_eq]
    rfl
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U U_in
    exact conj x₀ U_in
#align group_filter_basis.is_topological_group GroupFilterBasis.isTopologicalGroup

structure coming from
a ring filter basis then it's a topological ring. -/
instance (priority := 100) isTopologicalRing {R : Type u} [Ring R] (B : RingFilterBasis R) :
    @TopologicalRing R B.topology _ := by
  let B' := B.toAddGroupFilterBasis
  letI := B'.topology
  have basis := B'.nhds_zero_hasBasis
  have basis' := basis.prod basis
  haveI := B'.isTopologicalAddGroup
  apply TopologicalRing.of_addGroup_of_nhds_zero
  · rw [basis'.tendsto_iff basis]
    suffices ∀ U ∈ B', ∃ V W, (V ∈ B' ∧ W ∈ B') ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U by simpa
    intro U U_in
    rcases B.mul U_in with ⟨V, V_in, hV⟩
    refine' ⟨V, V, ⟨V_in, V_in⟩, _⟩
    intro a b a_in b_in
    exact hV <| mul_mem_mul a_in b_in
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U
    simpa using B.mul_left x₀
  · intro x₀
    rw [basis.tendsto_iff basis]
    intro U
    simpa using B.mul_right x₀
#align ring_filter_basis.is_topological_ring RingFilterBasis.isTopologicalRing

structure on `M`. -/
structure ModuleFilterBasis (R M : Type*) [CommRing R] [TopologicalSpace R] [AddCommGroup M]
  [Module R M] extends AddGroupFilterBasis M where
  smul' : ∀ {U}, U ∈ sets → ∃ V ∈ 𝓝 (0 : R), ∃ W ∈ sets, V • W ⊆ U
  smul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ • x) ⁻¹' U
  smul_right' : ∀ (m₀ : M) {U}, U ∈ sets → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ U
#align module_filter_basis ModuleFilterBasis

structure coming from
a module filter basis then it's a topological module. -/
instance (priority := 100) continuousSMul [TopologicalRing R] :
    @ContinuousSMul R M _ _ B.topology := by
  let B' := B.toAddGroupFilterBasis
  let _ := B'.topology
  have _ := B'.isTopologicalAddGroup
  exact ContinuousSMul.of_basis_zero B'.nhds_zero_hasBasis
      (fun {_} => by simpa using B.smul)
      (by simpa using B.smul_left) B.smul_right
#align module_filter_basis.has_continuous_smul ModuleFilterBasis.continuousSMul