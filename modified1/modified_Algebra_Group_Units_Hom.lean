def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u => ⟨f u.val, f u.inv,
      by rw [← f.map_mul, u.val_inv, f.map_one],
      by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_mul x y)
#align units.map Units.map

def coeHom : Mˣ →* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul
#align units.coe_hom Units.coeHom

def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := by ext; rw [h 1]; exact f.map_one
  map_mul' x y := Units.ext <| by simp only [h, val_mul, f.map_mul]
#align units.lift_right Units.liftRight

def toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) : G →* Mˣ :=
  Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_self _),
    map_mul_eq_one f (inv_mul_self _)⟩)
    fun _ => rfl
#align monoid_hom.to_hom_units MonoidHom.toHomUnits

def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl
#align is_unit.lift_right IsUnit.liftRight