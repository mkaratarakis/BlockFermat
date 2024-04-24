def symm : I → I := fun t => ⟨1 - t, mem_iff_one_sub_mem.mp t.prop⟩
#align unit_interval.symm unitInterval.symm

def symmHomeomorph : I ≃ₜ I where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

theorem strictAnti_symm : StrictAnti σ := fun _ _ h ↦ sub_lt_sub_left (α := ℝ) h _

-- 2024-02-27
@[deprecated] alias involutive_symm := symm_involutive

-- 2024-02-27
@[deprecated] alias bijective_symm := symm_bijective

theorem half_le_symm_iff (t : I) : 1 / 2 ≤ (σ t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 := by
  rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le, sub_half]

instance : ConnectedSpace I :=
  Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

/-- Verify there is an instance for `CompactSpace I`. -/
example : CompactSpace I := by infer_instance

theorem nonneg (x : I) : 0 ≤ (x : ℝ) :=
  x.2.1
#align unit_interval.nonneg unitInterval.nonneg

def addNSMul (δ : α) (n : ℕ) : Icc a b := projIcc a b h (a + n • δ)

lemma addNSMul_zero : addNSMul h δ 0 = a := by
  rw [addNSMul, zero_smul, add_zero, projIcc_left]

lemma addNSMul_eq_right [Archimedean α] (hδ : 0 < δ) :
    ∃ m, ∀ n ≥ m, addNSMul h δ n = b := by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn ↦ ?_⟩
  rw [addNSMul, coe_projIcc, add_comm, min_eq_left_iff.mpr, max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)

lemma monotone_addNSMul (hδ : 0 ≤ δ) : Monotone (addNSMul h δ) :=
  fun _ _ hnm ↦ monotone_projIcc h <| (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)

lemma abs_sub_addNSMul_le (hδ : 0 ≤ δ) {t : Icc a b} (n : ℕ)
    (ht : t ∈ Icc (addNSMul h δ n) (addNSMul h δ (n+1))) :
    (|t - addNSMul h δ n| : α) ≤ δ :=
  (abs_eq_self.2 <| sub_nonneg.2 ht.1).trans_le <| (sub_le_sub_right (by exact ht.2) _).trans <|
    (le_abs_self _).trans <| (abs_projIcc_sub_projIcc h).trans <| by
      rw [add_sub_add_comm, sub_self, zero_add, succ_nsmul', add_sub_cancel_right]
      exact (abs_eq_self.mpr hδ).le

end Set.Icc

open scoped unitInterval

/-- Any open cover `c` of a closed interval `[a, b]` in ℝ can be refined to
  a finite partition into subintervals. -/
lemma exists_monotone_Icc_subset_open_cover_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → Icc a b, t 0 = a ∧
      Monotone t ∧ (∃ m, ∀ n ≥ m, t n = b) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ/2) n) trivial
  exact ⟨i, fun t ht ↦ hsub ((abs_sub_addNSMul_le h hδ.le n ht).trans_lt <| half_lt_self δ_pos)⟩

/-- Any open cover of the unit interval can be refined to a finite partition into subintervals. -/
lemma exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧
      Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂

lemma exists_monotone_Icc_subset_open_cover_unitInterval_prod_self {ι} {c : ι → Set (I × I)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : ℝ) ≤ 1 := zero_le_one
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n m ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ/2) n, addNSMul h (δ/2) m) trivial
  exact ⟨i, fun t ht ↦ hsub (Metric.mem_ball.mpr <| (max_le (abs_sub_addNSMul_le h hδ.le n ht.1) <|
    abs_sub_addNSMul_le h hδ.le m ht.2).trans_lt <| half_lt_self δ_pos)⟩

end partition

@[simp]
theorem projIcc_eq_zero {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
  projIcc_eq_left zero_lt_one
#align proj_Icc_eq_zero projIcc_eq_zero

def tactic
/-- A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`. -/
macro "unit_interval" : tactic =>
  `(tactic| (first
  | apply unitInterval.nonneg
  | apply unitInterval.one_minus_nonneg
  | apply unitInterval.le_one
  | apply unitInterval.one_minus_le_one))
#noalign tactic.interactive.unit_interval

def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine' (e.trans _).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp
set_option linter.uppercaseLean3 false in
#align Icc_homeo_I iccHomeoI