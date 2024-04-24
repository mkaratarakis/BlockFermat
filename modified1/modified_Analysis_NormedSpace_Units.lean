def oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : ℕ, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h
#align units.one_sub Units.oneSub

def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := norm_mul_le (x⁻¹).1 _
        _ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by nlinarith only [h, hpos]
        _ = 1 := mul_inv_cancel (ne_of_gt hpos)))
    (x + t) (by simp [mul_add]) _ rfl
#align units.add Units.add

def ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  (x.add (y - x : R) h).copy y (by simp) _ rfl
#align units.unit_of_nearby Units.ofNearby