def RingAut (R : Type*) [Mul R] [Add R] :=
  RingEquiv R R
#align ring_aut RingAut

def toAddAut : RingAut R →* AddAut R := by
  refine'
  { toFun := RingEquiv.toAddEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_add_aut RingAut.toAddAut

def toMulAut : RingAut R →* MulAut R := by
  refine'
  { toFun := RingEquiv.toMulEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_mul_aut RingAut.toMulAut

def toPerm : RingAut R →* Equiv.Perm R := by
  refine'
  { toFun := RingEquiv.toEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_perm RingAut.toPerm

def (f : RingAut R) (r : R) : f • r = f r :=
  rfl
#align ring_aut.smul_def RingAut.smul_def

def _root_.MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G →* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
  map_mul' g h := RingEquiv.ext <| mul_smul g h
  map_one' := RingEquiv.ext <| one_smul _
#align mul_semiring_action.to_ring_aut MulSemiringAction.toRingAut

structure on `RingAut R := RingEquiv R R`.

## Implementation notes

structure is defined.

## Tags