def diam (s : Set α) : ℝ :=
  ENNReal.toReal (EMetric.diam s)
#align metric.diam Metric.diam

def evalDiam : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Metric.diam _ $inst $s) =>
    assertInstancesCommute
    pure (.nonnegative q(Metric.diam_nonneg))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

open Metric

theorem Metric.cobounded_eq_cocompact [ProperSpace α] : cobounded α = cocompact α := by
  nontriviality α; inhabit α
  exact cobounded_le_cocompact.antisymm <| (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ ↦ (isCompact_closedBall _ _).compl_mem_cocompact
#align comap_dist_right_at_top_eq_cocompact Metric.cobounded_eq_cocompact

structure give the same topology, any order-bounded set is metric-bounded. -/
theorem isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    IsBounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)
#align metric.bounded_of_bdd_above_of_bdd_below Metric.isBounded_of_bddAbove_of_bddBelow