def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }
#align mul_semiring_action.to_ring_hom MulSemiringAction.toRingHom

def (f : R →+* R) (a : R) : f • a = f a :=
  rfl
#align ring_hom.smul_def RingHom.smul_def

def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
#align mul_semiring_action.to_ring_equiv MulSemiringAction.toRingEquiv

def MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }
#align mul_semiring_action.comp_hom MulSemiringAction.compHom