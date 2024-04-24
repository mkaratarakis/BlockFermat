def powMonoidHom (n : ℕ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n
#align pow_monoid_hom powMonoidHom

def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n
#align zpow_group_hom zpowGroupHom