def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | snorm f p μ < ∞ }
  zero_mem' := by simp [snorm_congr_ae AEEqFun.coeFn_zero, snorm_zero]
  add_mem' {f g} hf hg := by
    simp [snorm_congr_ae (AEEqFun.coeFn_add f g),
      snorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_setOf_eq, snorm_congr_ae (AEEqFun.coeFn_neg f), snorm_neg]
#align measure_theory.Lp MeasureTheory.Lp

def toLp (f : α → E) (h_mem_ℒp : Memℒp f p μ) : Lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩
#align measure_theory.mem_ℒp.to_Lp MeasureTheory.Memℒp.toLp

def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (snorm f p μ) :=
  rfl
#align measure_theory.Lp.norm_def MeasureTheory.Lp.norm_def

def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (snorm f p μ) :=
  rfl
#align measure_theory.Lp.nnnorm_def MeasureTheory.Lp.nnnorm_def

def (f g : Lp E p μ) : dist f g = (snorm (⇑f - ⇑g) p μ).toReal := by
  simp_rw [dist, norm_def]
  refine congr_arg _ ?_
  apply snorm_congr_ae (coeFn_sub _ _)
#align measure_theory.Lp.dist_def MeasureTheory.Lp.dist_def

def (f g : Lp E p μ) : edist f g = snorm (⇑f - ⇑g) p μ :=
  rfl
#align measure_theory.Lp.edist_def MeasureTheory.Lp.edist_def

def ..

@[simp]
theorem edist_toLp_toLp (f g : α → E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = snorm (f - g) p μ := by
  rw [edist_def]
  exact snorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)
#align measure_theory.Lp.edist_to_Lp_to_Lp MeasureTheory.Lp.edist_toLp_toLp

def LpSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }
#align measure_theory.Lp.Lp_submodule MeasureTheory.Lp.LpSubmodule

def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  Memℒp.toLp (s.indicator fun _ => c) (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.indicator_const_Lp MeasureTheory.indicatorConstLp

def Lp.const : E →+ Lp E p μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma Lp.coeFn_const : Lp.const p μ c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

@[simp] lemma Lp.const_val : (Lp.const p μ c).1 = AEEqFun.const α c := rfl

@[simp]
lemma Memℒp.toLp_const : Memℒp.toLp _ (memℒp_const c) = Lp.const p μ c := rfl

@[simp]
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← Memℒp.toLp_const, indicatorConstLp]
  simp only [Set.indicator_univ, Function.const]

theorem Lp.norm_const [NeZero μ] (hp_zero : p ≠ 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  rw [← Memℒp.toLp_const, Lp.norm_toLp, snorm_const] <;> try assumption
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow, coe_nnnorm]

theorem Lp.norm_const' (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← Memℒp.toLp_const, Lp.norm_toLp, snorm_const'] <;> try assumption
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow, coe_nnnorm]

theorem Lp.norm_const_le : ‖Lp.const p μ c‖ ≤ ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

/-- `MeasureTheory.Lp.const` as a `LinearMap`. -/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E] :
    E →ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

@[simps! apply]
protected def Lp.constL (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    E →L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous ((μ Set.univ).toReal ^ (1 / p.toReal)) fun _ ↦
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 ≤ p)] :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ (μ Set.univ).toReal ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end const

theorem Memℒp.norm_rpow_div {f : α → E} (hf : Memℒp f p μ) (q : ℝ≥0∞) :
    Memℒp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ := by
  refine' ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, _⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp [q_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exact (memℒp_top_const (1 : ℝ)).2
  rw [snorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne
#align measure_theory.mem_ℒp.norm_rpow_div MeasureTheory.Memℒp.norm_rpow_div

def compMeasurePreserving (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →+ Lp E p μ where
  toFun g := ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]
theorem compMeasurePreserving_val (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    (compMeasurePreserving f hf g).1 = g.1.compMeasurePreserving f hf :=
  rfl

theorem coeFn_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf g =ᵐ[μ] g ∘ f :=
  g.1.coeFn_compMeasurePreserving hf

@[simp]
theorem norm_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    ‖compMeasurePreserving f hf g‖ = ‖g‖ :=
  congr_arg ENNReal.toReal <| g.1.snorm_compMeasurePreserving hf

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear map. -/
@[simps]
def compMeasurePreservingₗ (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗ[𝕜] Lp E p μ where
  __ := compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear isometry. -/
@[simps!]
def compMeasurePreservingₗᵢ [Fact (1 ≤ p)] (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗᵢ[𝕜] Lp E p μ where
  toLinearMap := compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)

end Lp

end MeasureTheory

open MeasureTheory

/-!
### Composition on `L^p`

def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E), by
    suffices ∀ᵐ x ∂μ, ‖AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖ from
      Lp.mem_Lp_of_ae_le_mul this
    filter_upwards [AEEqFun.coeFn_comp g hg.continuous (f : α →ₘ[μ] E)] with a ha
    simp only [ha]
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    exact hg.dist_le_mul (f a) 0⟩
#align lipschitz_with.comp_Lp LipschitzWith.compLp

def compLp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.compLp (map_zero L) f
#align continuous_linear_map.comp_Lp ContinuousLinearMap.compLp

def compLpₗ (L : E →L[𝕜] F) : Lp E p μ →ₗ[𝕜] Lp F p μ where
  toFun f := L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := by
    dsimp
    ext1
    filter_upwards [Lp.coeFn_smul c f, coeFn_compLp L (c • f), Lp.coeFn_smul c (L.compLp f),
      coeFn_compLp L f] with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, map_smul, Pi.smul_apply]
#align continuous_linear_map.comp_Lpₗ ContinuousLinearMap.compLpₗ

def compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) : Lp E p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le
#align continuous_linear_map.comp_LpL ContinuousLinearMap.compLpL

def posPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f
#align measure_theory.Lp.pos_part MeasureTheory.Lp.posPart

def negPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  posPart (-f)
#align measure_theory.Lp.neg_part MeasureTheory.Lp.negPart

def MeasureTheory.Lp.boundedContinuousFunction : AddSubgroup (Lp E p μ) :=
  AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E)).range (Lp E p μ)
#align measure_theory.Lp.bounded_continuous_function MeasureTheory.Lp.boundedContinuousFunction

def toLpHom [Fact (1 ≤ p)] : NormedAddGroupHom (α →ᵇ E) (Lp E p μ) :=
  { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E))
      (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }
#align bounded_continuous_function.to_Lp_hom BoundedContinuousFunction.toLpHom

def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : (α →ᵇ E) →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule E p μ 𝕜)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le
#align bounded_continuous_function.to_Lp BoundedContinuousFunction.toLp

def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : C(α, E) →L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.to_Lp ContinuousMap.toLp

def [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =
      BoundedContinuousFunction.toLp (E := E) p μ 𝕜 (linearIsometryBoundedOfCompact α E 𝕜 f) :=
  rfl
#align continuous_map.to_Lp_def ContinuousMap.toLp_def

structure from `BoundedContinuousFunction.toLp` along the isometry. -/
def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : C(α, E) →L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.to_Lp ContinuousMap.toLp