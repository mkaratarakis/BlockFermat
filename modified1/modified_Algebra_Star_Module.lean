def starLinearEquiv (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] : A ≃ₗ⋆[R] A :=
  { starAddEquiv with
    toFun := star
    map_smul' := star_smul }
#align star_linear_equiv starLinearEquiv

def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }
#align self_adjoint.submodule selfAdjoint.submodule

def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }
#align skew_adjoint.submodule skewAdjoint.submodule

def selfAdjointPart : A →ₗ[R] selfAdjoint A where
  toFun x :=
    ⟨(⅟ 2 : R) • (x + star x), by
      simp only [selfAdjoint.mem_iff, star_smul, add_comm, StarAddMonoid.star_add, star_inv',
        star_bit0, star_one, star_star, star_invOf (2 : R), star_trivial]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟ 2 * r = r * ⅟ 2 from Commute.invOf_left <| (2 : ℕ).cast_commute r]
#align self_adjoint_part selfAdjointPart

def skewAdjointPart : A →ₗ[R] skewAdjoint A where
  toFun x :=
    ⟨(⅟ 2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_mk,
      AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [← mul_smul, ← smul_sub,
      show r * ⅟ 2 = ⅟ 2 * r from Commute.invOf_right <| (2 : ℕ).commute_cast r]
#align skew_adjoint_part skewAdjointPart

def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A := by
  refine LinearEquiv.ofLinear ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  -- Note: with #6965 `Submodule.coeSubtype` doesn't fire in `dsimp` or `simp`