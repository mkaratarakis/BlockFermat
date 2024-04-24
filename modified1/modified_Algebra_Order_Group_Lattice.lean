def CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α]
    [CovariantClass α α (· * ·) (· ≤ ·)] : DistribLattice α where
  le_sup_inf x y z := by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
      le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_right) inf_le_right
#align lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice CommGroup.toDistribLattice