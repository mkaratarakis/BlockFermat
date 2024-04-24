def powMonoidWithZeroHom : M →*₀ M :=
  { powMonoidHom n with map_zero' := zero_pow hn }
#align pow_monoid_with_zero_hom powMonoidWithZeroHom