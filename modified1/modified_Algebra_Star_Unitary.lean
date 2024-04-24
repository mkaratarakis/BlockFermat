def unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_setOf_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine' ⟨_, _⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]
#align unitary unitary

def toUnits : unitary R →* Rˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
#align unitary.to_units unitary.toUnits

def map : unitary R →* unitary S where
  toFun := Subtype.map f (fun _ ↦ map_mem f)
  map_one' := Subtype.ext <| map_one f
  map_mul' _ _ := Subtype.ext <| map_mul f _ _

lemma toUnits_comp_map : toUnits.comp (map f) = (Units.map f).comp toUnits := by ext; rfl

end Map

section CommMonoid

variable [CommMonoid R] [StarMul R]

instance : CommGroup (unitary R) :=
  { inferInstanceAs (Group (unitary R)), Submonoid.toCommMonoid _ with }

theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h
#align unitary.mem_iff_star_mul_self unitary.mem_iff_star_mul_self