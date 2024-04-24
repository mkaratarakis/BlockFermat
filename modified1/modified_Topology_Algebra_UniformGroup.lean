def TopologicalGroup.toUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.2 / p.1)⁻¹) (comap (fun p : G × G ↦ p.2 / p.1) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by simp only [comap_comap, (· ∘ ·), nhds_translation_div]
#align topological_group.to_uniform_space TopologicalGroup.toUniformSpace

structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[TopologicalSpace α] [TopologicalGroup α]` since every topological
group naturally induces a uniform structure.

## Main declarations

structure on the
quotient obtained via other means.  -/
@[to_additive "The quotient `G ⧸ N` of a complete first countable uniform additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. In contrast to `QuotientAddGroup.completeSpace'`, in this version
`G` is already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `TopologicalAddGroup.toUniformSpace`.
In the most common use case ─ quotients of normed additive commutative groups by subgroups ─
significant care was taken so that the uniform structure inherent in that setting coincides
(definitionally) with the uniform structure provided here."]
instance QuotientGroup.completeSpace (G : Type u) [Group G] [us : UniformSpace G] [UniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.Normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) := by
  rw [← @UniformGroup.toUniformSpace_eq _ us _ _] at hG
  infer_instance
#align quotient_group.complete_space QuotientGroup.completeSpace