def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := @inv_le_inv_iff α _ _ _ _ _ _
#align order_iso.inv OrderIso.inv

def OrderIso.divLeft (a : α) : α ≃o αᵒᵈ where
  toEquiv := (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := @div_le_div_iff_left α _ _ _ _ _ _ _
#align order_iso.div_left OrderIso.divLeft

def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a
#align order_iso.mul_right OrderIso.mulRight

def OrderIso.divRight (a : α) : α ≃o α where
  toEquiv := Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a
#align order_iso.div_right OrderIso.divRight

def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a
#align order_iso.mul_left OrderIso.mulLeft