def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ I.pi ι → (ι' → R) ⧸ I.pi ι' := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk (I.pi ι') (e y))
    (by
      refine' fun a b hab => Ideal.Quotient.eq.2 fun h => _
      rw [Submodule.quotientRel_r_def] at hab
      rw [← LinearMap.map_sub]
      exact Ideal.map_pi _ _ hab e h)
#noalign induced_map

def induced_equiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] (ι' → R) ⧸ I.pi ι' := by
  refine'
    { toFun := induced_map I e
      invFun := induced_map I e.symm.. }
  all_goals
    first |rintro ⟨a⟩ ⟨b⟩|rintro ⟨a⟩
  -- Porting note: the next 4 lines were necessary because Lean couldn't correctly infer `(I.pi ι)`
  -- and `(I.pi ι')` on its own.
  pick_goal 3
  convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
  congr
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  all_goals
    convert_to Ideal.Quotient.mk (I.pi ι') _ = Ideal.Quotient.mk (I.pi ι') _
    congr
    simp only [map_add, LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ, RingHom.id_apply,
      LinearEquiv.apply_symm_apply]
#noalign induced_equiv