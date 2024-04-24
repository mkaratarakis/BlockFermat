def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)
#align subsemigroup.unit_ball Subsemigroup.unitBall

def Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one hx (norm_nonneg _) hy)
#align subsemigroup.unit_closed_ball Subsemigroup.unitClosedBall

def Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }
#align submonoid.unit_closed_ball Submonoid.unitClosedBall

def Submonoid.unitSphere (𝕜 : Type*) [NormedDivisionRing 𝕜] : Submonoid 𝕜
    where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one
#align submonoid.unit_sphere Submonoid.unitSphere

def unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl
#align unit_sphere_to_units unitSphereToUnits