def simpleFunc : AddSubgroup (Lp E p μ) where
  carrier := { f : Lp E p μ | ∃ s : α →ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α →ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add, AEEqFun.mk_eq_mk,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro f ⟨s, hs⟩
    use -s
    simp only [← hs, AEEqFun.neg_mk, SimpleFunc.coe_neg, AEEqFun.mk_eq_mk, AddSubgroup.coe_neg]
#align measure_theory.Lp.simple_func MeasureTheory.Lp.simpleFunc

def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩
#align measure_theory.Lp.simple_func.has_smul MeasureTheory.Lp.simpleFunc.smul

def module : Module 𝕜 (Lp.simpleFunc E p μ) where
  one_smul f := by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _
#align measure_theory.Lp.simple_func.module MeasureTheory.Lp.simpleFunc.module

def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩
#align measure_theory.Lp.simple_func.normed_space MeasureTheory.Lp.simpleFunc.normedSpace

def toLp (f : α →ₛ E) (hf : Memℒp f p μ) : Lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩
#align measure_theory.Lp.simple_func.to_Lp MeasureTheory.Lp.simpleFunc.toLp

def toSimpleFunc (f : Lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2
#align measure_theory.Lp.simple_func.to_simple_func MeasureTheory.Lp.simpleFunc.toSimpleFunc

def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.Lp.simple_func.indicator_const MeasureTheory.Lp.simpleFunc.indicatorConst

def coeToLp : Lp.simpleFunc E p μ →L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl
    cont := Lp.simpleFunc.uniformContinuous.continuous }
#align measure_theory.Lp.simple_func.coe_to_Lp MeasureTheory.Lp.simpleFunc.coeToLp

def coeSimpleFuncNonnegToLpNonneg :
    { g : Lp.simpleFunc G p μ // 0 ≤ g } → { g : Lp G p μ // 0 ≤ g } := fun g => ⟨g, g.2⟩
#align measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg

structure on `Lp.simpleFunc E p μ`, would be
unnecessary.  But instead, `Lp.simpleFunc E p μ` is defined as an `AddSubgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩
#align measure_theory.Lp.simple_func.has_smul MeasureTheory.Lp.simpleFunc.smul