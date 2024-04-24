def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_iSup` needed some help
      refine
        iSup_le fun i => (edist_triangle _ (g i) _).trans <| add_le_add
            (le_iSup (fun k => edist (f k) (g k)) i) (le_iSup (fun k => edist (g k) (h k)) i)
    · simp only [edist_eq_sum (zero_lt_one.trans_le hp)]
      calc
        (∑ i, edist (f i) (h i) ^ p.toReal) ^ (1 / p.toReal) ≤
            (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          apply edist_triangle
        _ ≤
            (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) +
              (∑ i, edist (g i) (h i) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.Lp_add_le _ _ _ hp
#align pi_Lp.pseudo_emetric_aux PiLp.pseudoEmetricAux

def pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · exact iSup_edist_ne_top_aux f g
      · rw [edist_eq_sum (zero_lt_one.trans_le h)]
        exact
          ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (zero_le_one.trans h))
            (ne_of_lt <|
              ENNReal.sum_lt_top fun i hi =>
                ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)))
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_iSup, dist_eq_iSup]
      · cases isEmpty_or_nonempty ι
        · simp only [Real.iSup_of_isEmpty, ciSup_of_empty, ENNReal.bot_eq_zero, ENNReal.zero_toReal]
        · refine' le_antisymm (ciSup_le fun i => _) _
          · rw [← ENNReal.ofReal_le_iff_le_toReal (iSup_edist_ne_top_aux f g), ←
              PseudoMetricSpace.edist_dist]
            -- Porting note: `le_iSup` needed some help
            exact le_iSup (fun k => edist (f k) (g k)) i
          · refine' ENNReal.toReal_le_of_le_ofReal (Real.sSup_nonneg _ _) (iSup_le fun i => _)
            · rintro - ⟨i, rfl⟩
              exact dist_nonneg
            · change PseudoMetricSpace.edist _ _ ≤ _
              rw [PseudoMetricSpace.edist_dist]
              -- Porting note: `le_ciSup` needed some help
              exact ENNReal.ofReal_le_ofReal
                (le_ciSup (Finite.bddAbove_range (fun k => dist (f k) (g k))) i)
    · have A : ∀ i, edist (f i) (g i) ^ p.toReal ≠ ⊤ := fun i =>
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [edist_eq_sum (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        dist_eq_sum (zero_lt_one.trans_le h), ← ENNReal.toReal_sum fun i _ => A i]
#align pi_Lp.pseudo_metric_aux PiLp.pseudoMetricAux

def equivₗᵢ : PiLp ∞ β ≃ₗᵢ[𝕜] ∀ i, β i :=
  { WithLp.equiv ∞ (∀ i, β i) with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl
    norm_map' := norm_equiv }
#align pi_Lp.equivₗᵢ PiLp.equivₗᵢ

def _root_.LinearIsometryEquiv.piLpCongrLeft (e : ι ≃ ι') :
    (PiLp p fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p fun _ : ι' => E where
  toLinearEquiv := LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum (zero_lt_one.trans_le h)]
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
#align linear_isometry_equiv.pi_Lp_congr_left LinearIsometryEquiv.piLpCongrLeft

def continuousLinearEquiv : PiLp p β ≃L[𝕜] ∀ i, β i where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := continuous_equiv _ _
  continuous_invFun := continuous_equiv_symm _ _
#align pi_Lp.continuous_linear_equiv PiLp.continuousLinearEquiv

def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
  Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι → 𝕜))
#align pi_Lp.basis_fun PiLp.basisFun

structure on `PiLp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

## Implementation notes

structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : EDist (PiLp p β) where
  edist f g :=
    if p = 0 then {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {β}

theorem edist_eq_card (f g : PiLp 0 β) :
    edist f g = {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl
#align pi_Lp.edist_eq_card PiLp.edist_eq_card

structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : Dist (PiLp p α) where
  dist f g :=
    if p = 0 then {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {α}

theorem dist_eq_card (f g : PiLp 0 α) :
    dist f g = {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl
#align pi_Lp.dist_eq_card PiLp.dist_eq_card

structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (PiLp p β) where
  norm f :=
    if p = 0 then {i | ‖f i‖ ≠ 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
#align pi_Lp.has_norm PiLp.instNorm

structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [Fact (1 ≤ p)] [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]
variable [Fintype ι]

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_iSup` needed some help
      refine
        iSup_le fun i => (edist_triangle _ (g i) _).trans <| add_le_add
            (le_iSup (fun k => edist (f k) (g k)) i) (le_iSup (fun k => edist (g k) (h k)) i)
    · simp only [edist_eq_sum (zero_lt_one.trans_le hp)]
      calc
        (∑ i, edist (f i) (h i) ^ p.toReal) ^ (1 / p.toReal) ≤
            (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          apply edist_triangle
        _ ≤
            (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) +
              (∑ i, edist (g i) (h i) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.Lp_add_le _ _ _ hp
#align pi_Lp.pseudo_emetric_aux PiLp.pseudoEmetricAux

structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
@[reducible]
def pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · exact iSup_edist_ne_top_aux f g
      · rw [edist_eq_sum (zero_lt_one.trans_le h)]
        exact
          ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (zero_le_one.trans h))
            (ne_of_lt <|
              ENNReal.sum_lt_top fun i hi =>
                ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)))
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_iSup, dist_eq_iSup]
      · cases isEmpty_or_nonempty ι
        · simp only [Real.iSup_of_isEmpty, ciSup_of_empty, ENNReal.bot_eq_zero, ENNReal.zero_toReal]
        · refine' le_antisymm (ciSup_le fun i => _) _
          · rw [← ENNReal.ofReal_le_iff_le_toReal (iSup_edist_ne_top_aux f g), ←
              PseudoMetricSpace.edist_dist]
            -- Porting note: `le_iSup` needed some help
            exact le_iSup (fun k => edist (f k) (g k)) i
          · refine' ENNReal.toReal_le_of_le_ofReal (Real.sSup_nonneg _ _) (iSup_le fun i => _)
            · rintro - ⟨i, rfl⟩
              exact dist_nonneg
            · change PseudoMetricSpace.edist _ _ ≤ _
              rw [PseudoMetricSpace.edist_dist]
              -- Porting note: `le_ciSup` needed some help
              exact ENNReal.ofReal_le_ofReal
                (le_ciSup (Finite.bddAbove_range (fun k => dist (f k) (g k))) i)
    · have A : ∀ i, edist (f i) (g i) ^ p.toReal ≠ ⊤ := fun i =>
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [edist_eq_sum (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        dist_eq_sum (zero_lt_one.trans_le h), ← ENNReal.toReal_sum fun i _ => A i]
#align pi_Lp.pseudo_metric_aux PiLp.pseudoMetricAux