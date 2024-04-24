def orthogonalProjectionFn (v : E) :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose
#align orthogonal_projection_fn orthogonalProjectionFn

def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨orthogonalProjectionFn K v, orthogonalProjectionFn_mem v⟩
      map_add' := fun x y => by
        have hm : orthogonalProjectionFn K x + orthogonalProjectionFn K y ∈ K :=
          Submodule.add_mem K (orthogonalProjectionFn_mem x) (orthogonalProjectionFn_mem y)
        have ho :
          ∀ w ∈ K, ⟪x + y - (orthogonalProjectionFn K x + orthogonalProjectionFn K y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            orthogonalProjectionFn_inner_eq_zero _ w hw, add_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho]
      map_smul' := fun c x => by
        have hm : c • orthogonalProjectionFn K x ∈ K :=
          Submodule.smul_mem K _ (orthogonalProjectionFn_mem x)
        have ho : ∀ w ∈ K, ⟪c • x - c • orthogonalProjectionFn K x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            mul_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho] }
    1 fun x => by
    simp only [one_mul, LinearMap.coe_mk]
    refine' le_of_pow_le_pow_left two_ne_zero (norm_nonneg _) _
    change ‖orthogonalProjectionFn K x‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [orthogonalProjectionFn_norm_sq K x]
#align orthogonal_projection orthogonalProjection

def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.subtype.comp (orthogonalProjection K).toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul]
#align reflection_linear_equiv reflectionLinearEquivₓ

def reflection : E ≃ₗᵢ[𝕜] E :=
  { reflectionLinearEquiv K with
    norm_map' := by
      intro x
      dsimp only
      let w : K := orthogonalProjection K x
      let v := x - w
      have : ⟪v, w⟫ = 0 := orthogonalProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this using 2
      · rw [LinearEquiv.coe_mk, reflectionLinearEquiv, LinearEquiv.toFun_eq_coe,
          LinearEquiv.coe_ofInvolutive, LinearMap.sub_apply, LinearMap.id_apply, two_smul,
          LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          ContinuousLinearMap.coe_coe]
        dsimp [v]
        abel
      · simp only [v, add_sub_cancel, eq_self_iff_true] }
#align reflection reflection

def OrthogonalFamily.decomposition [DecidableEq ι] [Fintype ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)] (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (h : iSup V = ⊤) : DirectSum.Decomposition V
    where
  decompose' x := DFinsupp.equivFunOnFintype.symm fun i => orthogonalProjection (V i) x
  left_inv x := by
    dsimp only
    letI := fun i => Classical.decEq (V i)
    rw [DirectSum.coeAddMonoidHom, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644

structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of sequences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`.  -/
theorem Submodule.orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine' le_antisymm _ _
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure using 1
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal
#align submodule.orthogonal_orthogonal_eq_closure Submodule.orthogonal_orthogonal_eq_closure