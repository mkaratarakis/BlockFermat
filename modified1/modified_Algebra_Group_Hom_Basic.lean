def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv
#align inv_monoid_hom invMonoidHom

def ofMapMulInv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_right_inv, one_mul, inv_inv] }
#align monoid_hom.of_map_mul_inv MonoidHom.ofMapMulInv

def ofMapDiv {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)
#align monoid_hom.of_map_div MonoidHom.ofMapDiv