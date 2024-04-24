def pointwiseMulAction : MulAction α (Subgroup G) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f : Monoid.End G => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align subgroup.pointwise_mul_action Subgroup.pointwiseMulAction

def {a : α} (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) :=
  rfl
#align subgroup.pointwise_smul_def Subgroup.pointwise_smul_def

def equivSMul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G) :=
  (MulDistribMulAction.toMulEquiv G a).subgroupMap H
#align subgroup.equiv_smul Subgroup.equivSMul

def pointwiseMulAction : MulAction α (AddSubgroup A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align add_subgroup.pointwise_mul_action AddSubgroup.pointwiseMulAction