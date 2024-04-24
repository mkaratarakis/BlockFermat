def linearMapEquivFun : (M →ₗ[R] N) ≃ₗ[S] ChooseBasisIndex R M → N :=
  (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ LinearMap.ringLmapEquivSelf R S N

instance Module.Free.linearMap [Module.Free S N] : Module.Free S (M →ₗ[R] N) :=
  Module.Free.of_equiv (linearMapEquivFun R S M N).symm
#align module.free.linear_map Module.Free.linearMap