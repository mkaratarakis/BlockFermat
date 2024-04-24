def Fintype.groupWithZeroOfCancel (M : Type*) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M]
    [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [Inv.inv, dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp [Inv.inv, dif_pos rfl] }
#align fintype.group_with_zero_of_cancel Fintype.groupWithZeroOfCancel

def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R :=
  { show GroupWithZero R from Fintype.groupWithZeroOfCancel R, ‹Ring R› with
    qsmul := qsmulRec _}
#align fintype.division_ring_of_is_domain Fintype.divisionRingOfIsDomain

def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }
#align fintype.field_of_domain Fintype.fieldOfDomain