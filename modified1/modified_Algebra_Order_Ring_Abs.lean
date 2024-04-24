def absHom : α →*₀ α where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul
#align abs_hom absHom