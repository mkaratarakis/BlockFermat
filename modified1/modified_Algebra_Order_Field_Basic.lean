def OrderIso.mulLeft₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equiv.mulLeft₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_left ha }
#align order_iso.mul_left₀ OrderIso.mulLeft₀

def OrderIso.mulRight₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equiv.mulRight₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_right ha }
#align order_iso.mul_right₀ OrderIso.mulRight₀