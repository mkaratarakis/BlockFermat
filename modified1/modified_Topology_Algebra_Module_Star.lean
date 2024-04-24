def starL (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star
#align starL starL

def starL' (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [TrivialStar R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp [starRingEnd_apply]
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)
#align starL' starL'

def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R
  cont := continuous_selfAdjointPart _ _
#align self_adjoint_partL selfAdjointPartL

def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R
  cont := continuous_skewAdjointPart _ _
#align skew_adjoint_partL skewAdjointPartL

def StarModule.decomposeProdAdjointL [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
  continuous_toFun := continuous_decomposeProdAdjoint _ _
  continuous_invFun := continuous_decomposeProdAdjoint_symm _ _
#align star_module.decompose_prod_adjointL StarModule.decomposeProdAdjointL