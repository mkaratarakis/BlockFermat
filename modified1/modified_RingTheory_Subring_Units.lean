def Units.posSubgroup (R : Type*) [LinearOrderedSemiring R] : Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }
#align units.pos_subgroup Units.posSubgroup