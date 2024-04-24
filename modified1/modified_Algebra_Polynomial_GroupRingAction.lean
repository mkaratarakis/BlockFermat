def prodXSubSMul (x : R) : R[X] :=
  letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g ↦
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)
#align prod_X_sub_smul prodXSubSMul

def polynomial (g : P →+*[M] Q) : P[X] →+*[M] Q[X] where
  toFun := map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b ↦ by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq ↦ by
        rw [smul_add, Polynomial.map_add, ihp, ihq, Polynomial.map_add, smul_add])
      fun n b _ ↦ by rw [MonoidHom.id_apply, smul_mul', smul_C, smul_pow', smul_X,
        Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  -- Porting note: added `.toRingHom`
  map_zero' := Polynomial.map_zero g.toRingHom
  map_add' p q := Polynomial.map_add g.toRingHom
  map_one' := Polynomial.map_one g.toRingHom
  map_mul' p q := Polynomial.map_mul g.toRingHom
#align mul_semiring_action_hom.polynomial MulSemiringActionHom.polynomial