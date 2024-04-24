def equivIco : AddCircle p ≃ Ico a (a + p) :=
  QuotientAddGroup.equivIcoMod hp.out a
#align add_circle.equiv_Ico AddCircle.equivIco

def equivIoc : AddCircle p ≃ Ioc a (a + p) :=
  QuotientAddGroup.equivIocMod hp.out a
#align add_circle.equiv_Ioc AddCircle.equivIoc

def liftIco (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIco p a
#align add_circle.lift_Ico AddCircle.liftIco

def liftIoc (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIoc p a
#align add_circle.lift_Ioc AddCircle.liftIoc

def partialHomeomorphCoe [DiscreteTopology (zmultiples p)] :
    PartialHomeomorph 𝕜 (AddCircle p) where
  toFun := (↑)
  invFun := fun x ↦ equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx ↦ congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ ↦ (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact ContinuousAt.continuousOn
      (fun _ ↦ continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)

lemma isLocalHomeomorph_coe [DiscreteTopology (zmultiples p)] [DenselyOrdered 𝕜] :
    IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) := by
  intro a
  obtain ⟨b, hb1, hb2⟩ := exists_between (sub_lt_self a hp.out)
  exact ⟨partialHomeomorphCoe p b, ⟨hb2, lt_add_of_sub_right_lt hb1⟩, rfl⟩

end Continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
theorem coe_image_Ico_eq : ((↑) : 𝕜 → AddCircle p) '' Ico a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ
#align add_circle.coe_image_Ico_eq AddCircle.coe_image_Ico_eq

def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_coe, AddAut.mulRight_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]
#align add_circle.equiv_add_circle AddCircle.equivAddCircle

def homeomorphAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃ₜ AddCircle q :=
  ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_right (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_right (q⁻¹ * p))).quotient_lift _⟩

@[simp]
theorem homeomorphAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    homeomorphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem homeomorphAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (homeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl

variable [hp : Fact (0 < p)]

section FloorRing

variable [FloorRing 𝕜]

@[simp]
theorem coe_equivIco_mk_apply (x : 𝕜) :
    (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  toIcoMod_eq_fract_mul _ x
#align add_circle.coe_equiv_Ico_mk_apply AddCircle.coe_equivIco_mk_apply

def setAddOrderOfEquiv {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n } ≃ { m | m < n ∧ m.gcd n = 1 } :=
  Equiv.symm <|
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine' ⟨fun m₁ m₂ h => Subtype.ext _, fun u => _⟩
        · simp_rw [Subtype.ext_iff] at h
          rw [← sub_eq_zero, ← coe_sub, ← sub_mul, ← sub_div, ← Int.cast_natCast m₁,
            ← Int.cast_natCast m₂, ← Int.cast_sub, coe_eq_zero_iff] at h
          obtain ⟨m, hm⟩ := h
          rw [← mul_div_right_comm, eq_div_iff, mul_comm, ← zsmul_eq_mul, mul_smul_comm, ←
            nsmul_eq_mul, ← natCast_zsmul, smul_smul,
            (zsmul_strictMono_left hp.out).injective.eq_iff, mul_comm] at hm
          swap
          · exact Nat.cast_ne_zero.2 hn.ne'
          rw [← @Nat.cast_inj ℤ, ← sub_eq_zero]
          refine' Int.eq_zero_of_abs_lt_dvd ⟨_, hm.symm⟩ (abs_sub_lt_iff.2 ⟨_, _⟩) <;>
            apply (Int.sub_le_self _ <| Nat.cast_nonneg _).trans_lt (Nat.cast_lt.2 _)
          exacts [m₁.2.1, m₂.2.1]
        obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
        exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)
#align add_circle.set_add_order_of_equiv AddCircle.setAddOrderOfEquiv

def equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where
  toFun x := Quot.mk _ <| inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
    Quot.liftOn x (↑) <| by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
    Quot.ind <| by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)
#align add_circle.equiv_Icc_quot AddCircle.equivIccQuot

def homeoIccQuot : 𝕋 ≃ₜ Quot (EndpointIdent p a) where
  toEquiv := equivIccQuot p a
  continuous_toFun := by
    -- Porting note: was `simp_rw`
    rw [quotientMap_quotient_mk'.continuous_iff]
    simp_rw [continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [inducing_subtype_val.continuousWithinAt_iff]
    · apply continuous_left_toIocMod
    · apply continuous_right_toIcoMod
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)
#align add_circle.homeo_Icc_quot AddCircle.homeoIccQuot

structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

structure
 * Exponential equivalence to `Circle`

-/


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [LinearOrderedAddCommGroup 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

theorem continuous_right_toIcoMod : ContinuousWithinAt (toIcoMod hp a) (Ici x) x := by
  intro s h
  rw [Filter.mem_map, mem_nhdsWithin_iff_exists_mem_nhds_inter]
  haveI : Nontrivial 𝕜 := ⟨⟨0, p, hp.ne⟩⟩
  simp_rw [mem_nhds_iff_exists_Ioo_subset] at h ⊢
  obtain ⟨l, u, hxI, hIs⟩ := h
  let d := toIcoDiv hp a x • p
  have hd := toIcoMod_mem_Ico hp a x
  simp_rw [subset_def, mem_inter_iff]
  refine' ⟨_, ⟨l + d, min (a + p) u + d, _, fun x => id⟩, fun y => _⟩ <;>
    simp_rw [← sub_mem_Ioo_iff_left, mem_Ioo, lt_min_iff]
  · exact ⟨hxI.1, hd.2, hxI.2⟩
  · rintro ⟨h, h'⟩
    apply hIs
    rw [← toIcoMod_sub_zsmul, (toIcoMod_eq_self _).2]
    exacts [⟨h.1, h.2.2⟩, ⟨hd.1.trans (sub_le_sub_right h' _), h.2.1⟩]
#align continuous_right_to_Ico_mod continuous_right_toIcoMod