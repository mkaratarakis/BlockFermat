def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    simp only
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.unique_diff_at_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin I hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hx]
  continuousOn_coordChange i j := by
    refine' (contDiffOn_fderiv_coord_change I i j).continuousOn.comp
      ((i.1.continuousOn_extend I).mono _) _
    · rw [i.1.extend_source]; exact inter_subset_left _ _
    simp_rw [← i.1.extend_image_source_inter, mapsTo_image]
  coordChange_comp := by
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds I hxi (j.1.extend_source_mem_nhds I hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hxi, j.1.extend_left_inv I hxj]
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I k.2)
        (subset_maximalAtlas I j.2) hxk hxj).differentiableWithinAt le_top
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I j.2)
        (subset_maximalAtlas I i.2) hxj hxi).differentiableWithinAt le_top
    · intro x _; exact mem_range_self _
    · exact I.unique_diff_at_image
    · rw [Function.comp_apply, i.1.extend_left_inv I hxi]
#align tangent_bundle_core tangentBundleCore

def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl

lemma tangentCoordChange_self {x z : M} {v : E} (h : z ∈ (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z ∈ (extChartAt I w).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  have h' : extChartAt I x z ∈ ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change I y x h').differentiableWithinAt (by simp)).hasFDerivWithinAt

lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source ∩ (extChartAt I y).source) := by
  convert (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangentBundleCore I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unusedArguments]
def TangentSpace {𝕜} [NontriviallyNormedField 𝕜] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] (_x : M) : Type* := E
-- Porting note: was deriving TopologicalSpace, AddCommGroup, TopologicalAddGroup
#align tangent_space TangentSpace

def TangentBundle :=
  Bundle.TotalSpace E (TangentSpace I : M → Type _)
#align tangent_bundle TangentBundle

def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).continuousOn
        simp only [TangentSpace.fiberBundle, mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }
#align tangent_bundle_model_space_homeomorph tangentBundleModelSpaceHomeomorph

def inTangentCoordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)
#align in_tangent_coordinates inTangentCoordinates