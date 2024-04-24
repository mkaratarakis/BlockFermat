def toNat : Cardinal →*₀ ℕ :=
  ENat.toNat.comp toENat
#align cardinal.to_nat Cardinal.toNat