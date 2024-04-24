def pointwiseNeg : Neg (Submodule R M) where
  neg p :=
    { -p.toAddSubmonoid with
      smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }
#align submodule.has_pointwise_neg Submodule.pointwiseNeg

def involutivePointwiseNeg : InvolutiveNeg (Submodule R M)
    where
  neg := Neg.neg
  neg_neg _S := SetLike.coe_injective <| neg_neg _
#align submodule.has_involutive_pointwise_neg Submodule.involutivePointwiseNeg

def negOrderIso : Submodule R M ≃o Submodule R M
    where
  toEquiv := Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _
#align submodule.neg_order_iso Submodule.negOrderIso

def pointwiseDistribMulAction : DistribMulAction α (Submodule R M)
    where
  smul a S := S.map (DistribMulAction.toLinearMap R M a : M →ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
  smul_zero _a := map_bot _
  smul_add _a _S₁ _S₂ := map_sup _ _ _
#align submodule.pointwise_distrib_mul_action Submodule.pointwiseDistribMulAction

def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }
#align submodule.pointwise_mul_action_with_zero Submodule.pointwiseMulActionWithZero