def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}
#align finite_exts finiteExts

def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup (L ≃ₐ[K] L)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L
#align fixed_by_finite fixedByFinite

def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis (L ≃ₐ[K] L) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩
    use (IntermediateField.fixingSubgroup (E1 ⊔ E2)).carrier
    refine' ⟨⟨_, ⟨_, finiteDimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩
    rw [Set.subset_inter_iff]
    exact
      ⟨IntermediateField.fixingSubgroup.antimono le_sup_left,
        IntermediateField.fixingSubgroup.antimono le_sup_right⟩
#align gal_basis galBasis

def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis (L ≃ₐ[K] L) where
  toFilterBasis := galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    let F : IntermediateField K L := E.map σ.symm.toAlgHom
    refine' ⟨F.fixingSubgroup.carrier, ⟨⟨F.fixingSubgroup, ⟨F, _, rfl⟩, rfl⟩, fun g hg => _⟩⟩
    · have : FiniteDimensional K E := hE
      apply im_finiteDimensional σ.symm
    change σ * g * σ⁻¹ ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp; rw [← AlgEquiv.invFun_eq_symm]; rfl⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x
#align gal_group_basis galGroupBasis

structure
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

structure on
`L ≃ₐ[K] L` induced by the group filter basis `galGroupBasis K L` -/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace (L ≃ₐ[K] L) :=
  GroupFilterBasis.topology (galGroupBasis K L)
#align krull_topology krullTopology