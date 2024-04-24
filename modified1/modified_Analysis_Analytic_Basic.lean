def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun _ => x
#align formal_multilinear_series.sum FormalMultilinearSeries.sum

def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k in Finset.range n, p k fun _ : Fin k => x
#align formal_multilinear_series.partial_sum FormalMultilinearSeries.partialSum

def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (C : ℝ) (_ : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C), (r : ℝ≥0∞)
#align formal_multilinear_series.radius FormalMultilinearSeries.radius

def HasFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFPowerSeriesOnBall f p x r
#align has_fpower_series_at HasFPowerSeriesAt

def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x
#align analytic_at AnalyticAt

def AnalyticOn (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → AnalyticAt 𝕜 f x
#align analytic_on AnalyticOn

def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E[×l]→L[𝕜] E[×k]→L[𝕜] F := by
  let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by erw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  exact a (p (k + l))
#align formal_multilinear_series.change_origin_series_term FormalMultilinearSeries.changeOriginSeriesTerm

def changeOriginSeries (k : ℕ) : FormalMultilinearSeries 𝕜 E (E[×k]→L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2
#align formal_multilinear_series.change_origin_series FormalMultilinearSeries.changeOriginSeries

def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun k => (p.changeOriginSeries k).sum x
#align formal_multilinear_series.change_origin FormalMultilinearSeries.changeOrigin

def changeOriginIndexEquiv :
    (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) ≃ Σ n : ℕ, Finset (Fin n) where
  toFun s := ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (Fin.castIso <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEquiv.toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices ∀ k' l', k' = k → l' = l → ∀ (hkl : k + l = k' + l') (hs'),
        (⟨k', l', ⟨Finset.map (Fin.castIso hkl).toEquiv.toEmbedding s, hs'⟩⟩ :
          Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) = ⟨k, l, ⟨s, hs⟩⟩ by
      apply this <;> simp only [hs, add_tsub_cancel_right]
    rintro _ _ rfl rfl hkl hs'
    simp only [Equiv.refl_toEmbedding, Fin.castIso_refl, Finset.map_refl, eq_self_iff_true,
      OrderIso.refl_toEquiv, and_self_iff, heq_iff_eq]
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), Fin.castIso_to_equiv]
#align formal_multilinear_series.change_origin_index_equiv FormalMultilinearSeries.changeOriginIndexEquiv

def derivSeries : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) :=
  (continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
    |>.compFormalMultilinearSeries (p.changeOriginSeries 1)

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0}

theorem hasFPowerSeriesOnBall_changeOrigin (k : ℕ) (hr : 0 < p.radius) :
    HasFPowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this
#align formal_multilinear_series.has_fpower_series_on_ball_change_origin FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin

structure HasFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) :
    Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum :
    ∀ {y}, y ∈ EMetric.ball (0 : E) r → HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))
#align has_fpower_series_on_ball HasFPowerSeriesOnBall