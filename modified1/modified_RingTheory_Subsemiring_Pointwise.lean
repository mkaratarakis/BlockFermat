def pointwiseMulAction : MulAction M (Subsemiring R)
    where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subsemiring.pointwise_mul_action Subsemiring.pointwiseMulAction

def {a : M} (S : Subsemiring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
#align subsemiring.pointwise_smul_def Subsemiring.pointwise_smul_def