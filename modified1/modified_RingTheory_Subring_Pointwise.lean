def pointwiseMulAction : MulAction M (Subring R) where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subring.pointwise_mul_action Subring.pointwiseMulAction

def {a : M} (S : Subring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
#align subring.pointwise_smul_def Subring.pointwise_smul_def