def AdjoinRoot [CommRing R] (f : R[X]) : Type u :=
  Polynomial R ⧸ (span {f} : Ideal R[X])
#align adjoin_root AdjoinRoot

def mk : R[X] →+* AdjoinRoot f :=
  Ideal.Quotient.mk _
#align adjoin_root.mk AdjoinRoot.mk

def of : R →+* AdjoinRoot f :=
  (mk f).comp C
#align adjoin_root.of AdjoinRoot.of

def root : AdjoinRoot f :=
  mk f X
#align adjoin_root.root AdjoinRoot.root

def lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : AdjoinRoot f →+* S := by
  apply Ideal.Quotient.lift _ (eval₂RingHom i x)
  intro g H
  rcases mem_span_singleton.1 H with ⟨y, hy⟩
  rw [hy, RingHom.map_mul, coe_eval₂RingHom, h, zero_mul]
#align adjoin_root.lift AdjoinRoot.lift

def liftHom (x : S) (hfx : aeval x f = 0) : AdjoinRoot f →ₐ[R] S :=
  { lift (algebraMap R S) x hfx with
    commutes' := fun r => show lift _ _ hfx r = _ from lift_of hfx }
#align adjoin_root.lift_hom AdjoinRoot.liftHom

def q := by
    rw [← map_natCast (of f), ← map_intCast (of f), ← map_div₀, ← Rat.cast_def]; rfl
  qsmul := (· • ·)
  qsmul_def q x :=
    -- Porting note: I gave the explicit motive and changed `rw` to `simp`.
    AdjoinRoot.induction_on (C := fun y ↦ q • y = (of f) q * y) x fun p ↦ by
      simp only [smul_mk, of, RingHom.comp_apply, ← (mk f).map_mul, Polynomial.rat_smul_eq_C_mul]
#align adjoin_root.field AdjoinRoot.instField

def modByMonicHom (hg : g.Monic) : AdjoinRoot g →ₗ[R] R[X] :=
  (Submodule.liftQ _ (Polynomial.modByMonicHom g)
        fun f (hf : f ∈ (Ideal.span {g}).restrictScalars R) =>
        (mem_ker_modByMonic hg).mpr (Ideal.mem_span_singleton.mp hf)).comp <|
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {g} : Ideal R[X])).symm.toLinearMap
#align adjoin_root.mod_by_monic_hom AdjoinRoot.modByMonicHom

def powerBasisAux' (hg : g.Monic) : Basis (Fin g.natDegree) R (AdjoinRoot g) :=
  Basis.ofEquivFun
    { toFun := fun f i => (modByMonicHom hg f).coeff i
      invFun := fun c => mk g <| ∑ i : Fin g.natDegree, monomial i (c i)
      map_add' := fun f₁ f₂ =>
        funext fun i => by simp only [(modByMonicHom hg).map_add, coeff_add, Pi.add_apply]
      map_smul' := fun f₁ f₂ =>
        funext fun i => by
          simp only [(modByMonicHom hg).map_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]
      -- Porting note: another proof that I converted to tactic mode
      left_inv := by
        intro f
        induction f using AdjoinRoot.induction_on
        simp only [modByMonicHom_mk, sum_modByMonic_coeff hg degree_le_natDegree]
        refine (mk_eq_mk.mpr ?_).symm
        rw [modByMonic_eq_sub_mul_div _ hg, sub_sub_cancel]
        exact dvd_mul_right _ _
      right_inv := fun x =>
        funext fun i => by
          nontriviality R
          simp only [modByMonicHom_mk]
          rw [(modByMonic_eq_self_iff hg).mpr, finset_sum_coeff]
          · simp_rw [coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
          · simp_rw [← C_mul_X_pow_eq_monomial]
            exact (degree_eq_natDegree <| hg.ne_zero).symm ▸ degree_sum_fin_lt _ }
#align adjoin_root.power_basis_aux' AdjoinRoot.powerBasisAux'

def powerBasis' (hg : g.Monic) : PowerBasis R (AdjoinRoot g) where
  gen := root g
  dim := g.natDegree
  basis := powerBasisAux' hg
  basis_eq_pow i := by
    simp only [powerBasisAux', Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · rw [Function.update_same, monomial_one_right_eq_X_pow, (mk g).map_pow, mk_X]
    · intro j _ hj
      rw [← monomial_zero_right _]
      convert congr_arg _ (Function.update_noteq hj _ _)
    -- Fix `DecidableEq` mismatch
    · intros
      have := Finset.mem_univ i
      contradiction
#align adjoin_root.power_basis' AdjoinRoot.powerBasis'

def powerBasisAux (hf : f ≠ 0) : Basis (Fin f.natDegree) K (AdjoinRoot f) := by
  let f' := f * C f.leadingCoeff⁻¹
  have deg_f' : f'.natDegree = f.natDegree := by
    rw [natDegree_mul hf, natDegree_C, add_zero]
    · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]
  have minpoly_eq : minpoly K (root f) = f' := minpoly_root hf
  apply @Basis.mk _ _ _ fun i : Fin f.natDegree => root f ^ i.val
  · rw [← deg_f', ← minpoly_eq]
    exact linearIndependent_pow (root f)
  · rintro y -
    rw [← deg_f', ← minpoly_eq]
    apply (isIntegral_root hf).mem_span_pow
    obtain ⟨g⟩ := y
    use g
    rw [aeval_eq]
    rfl
#align adjoin_root.power_basis_aux AdjoinRoot.powerBasisAux

def powerBasis (hf : f ≠ 0) : PowerBasis K (AdjoinRoot f) where
  gen := root f
  dim := f.natDegree
  basis := powerBasisAux hf
  basis_eq_pow := by simp [powerBasisAux]
#align adjoin_root.power_basis AdjoinRoot.powerBasis

def Minpoly.toAdjoin : AdjoinRoot (minpoly R x) →ₐ[R] adjoin R ({x} : Set S) :=
  liftHom _ ⟨x, self_mem_adjoin_singleton R x⟩
    (by simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])
#align adjoin_root.minpoly.to_adjoin AdjoinRoot.Minpoly.toAdjoin

def equiv' (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0) :
    AdjoinRoot g ≃ₐ[R] S :=
  { AdjoinRoot.liftHom g pb.gen h₂ with
    toFun := AdjoinRoot.liftHom g pb.gen h₂
    invFun := pb.lift (root g) h₁
    -- Porting note: another term-mode proof converted to tactic-mode.
    left_inv := fun x => by
      induction x using AdjoinRoot.induction_on
      rw [liftHom_mk, pb.lift_aeval, aeval_eq]
    right_inv := fun x => by
      nontriviality S
      obtain ⟨f, _hf, rfl⟩ := pb.exists_eq_aeval x
      rw [pb.lift_aeval, aeval_eq, liftHom_mk] }
#align adjoin_root.equiv' AdjoinRoot.equiv'

def equiv (f : F[X]) (hf : f ≠ 0) :
    (AdjoinRoot f →ₐ[F] L) ≃ { x // x ∈ f.aroots L } :=
  (powerBasis hf).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [powerBasis_gen, minpoly_root hf, aroots_mul, aroots_C, add_zero, Equiv.refl_apply]
      exact (monic_mul_leadingCoeff_inv hf).ne_zero)
#align adjoin_root.equiv AdjoinRoot.equiv

def quotMapOfEquivQuotMapCMapSpanMk :
    AdjoinRoot f ⧸ I.map (of f) ≃+*
      AdjoinRoot f ⧸ (I.map (C : R →+* R[X])).map (Ideal.Quotient.mk (span {f})) :=
  Ideal.quotEquivOfEq (by rw [of, AdjoinRoot.mk, Ideal.map_map])
set_option linter.uppercaseLean3 false in
#align adjoin_root.quot_map_of_equiv_quot_map_C_map_span_mk AdjoinRoot.quotMapOfEquivQuotMapCMapSpanMk

def quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk :
    AdjoinRoot f ⧸ (I.map (C : R →+* R[X])).map (Ideal.Quotient.mk (span ({f} : Set R[X]))) ≃+*
      (R[X] ⧸ I.map (C : R →+* R[X])) ⧸
        (span ({f} : Set R[X])).map (Ideal.Quotient.mk (I.map (C : R →+* R[X]))) :=
  quotQuotEquivComm (Ideal.span ({f} : Set R[X])) (I.map (C : R →+* R[X]))
set_option linter.uppercaseLean3 false in
#align adjoin_root.quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk AdjoinRoot.quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk

def Polynomial.quotQuotEquivComm :
    (R ⧸ I)[X] ⧸ span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))) ≃+*
      (R[X] ⧸ (I.map C)) ⧸ span ({(Ideal.Quotient.mk (I.map C)) f} : Set (R[X] ⧸ (I.map C))) :=
  quotientEquiv (span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
    (span {Ideal.Quotient.mk (I.map Polynomial.C) f}) (polynomialQuotientEquivQuotientPolynomial I)
    (by
      rw [map_span, Set.image_singleton, RingEquiv.coe_toRingHom,
        polynomialQuotientEquivQuotientPolynomial_map_mk I f])
#align adjoin_root.polynomial.quot_quot_equiv_comm AdjoinRoot.Polynomial.quotQuotEquivComm

def quotAdjoinRootEquivQuotPolynomialQuot :
    AdjoinRoot f ⧸ I.map (of f) ≃+*
    (R ⧸ I)[X] ⧸ span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]) :=
  (quotMapOfEquivQuotMapCMapSpanMk I f).trans
    ((quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk I f).trans
      ((Ideal.quotEquivOfEq (by rw [map_span, Set.image_singleton])).trans
        (Polynomial.quotQuotEquivComm I f).symm))
#align adjoin_root.quot_adjoin_root_equiv_quot_polynomial_quot AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot

def quotEquivQuotMap (f : R[X]) (I : Ideal R) :
    (AdjoinRoot f ⧸ Ideal.map (of f) I) ≃ₐ[R]
      (R ⧸ I)[X] ⧸ Ideal.span ({Polynomial.map (Ideal.Quotient.mk I) f} : Set (R ⧸ I)[X]) :=
  AlgEquiv.ofRingEquiv
    (show ∀ x, (quotAdjoinRootEquivQuotPolynomialQuot I f) (algebraMap R _ x) = algebraMap R _ x
      from fun x => by
      have :
        algebraMap R (AdjoinRoot f ⧸ Ideal.map (of f) I) x =
          Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) I) ((mk f) (C x)) :=
        rfl
      rw [this, quotAdjoinRootEquivQuotPolynomialQuot_mk_of, map_C]
      -- Porting note: the following `rfl` was not needed
      rfl)
#align adjoin_root.quot_equiv_quot_map AdjoinRoot.quotEquivQuotMap

def quotientEquivQuotientMinpolyMap (pb : PowerBasis R S) (I : Ideal R) :
    (S ⧸ I.map (algebraMap R S)) ≃ₐ[R]
      Polynomial (R ⧸ I) ⧸
        Ideal.span ({(minpoly R pb.gen).map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))) :=
  (ofRingEquiv
        (show ∀ x,
            (Ideal.quotientEquiv _ (Ideal.map (AdjoinRoot.of (minpoly R pb.gen)) I)
                  (AdjoinRoot.equiv' (minpoly R pb.gen) pb
                        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
                        (minpoly.aeval _ _)).symm.toRingEquiv
                  (by rw [Ideal.map_map, AlgEquiv.toRingEquiv_eq_coe,
                      ← AlgEquiv.coe_ringHom_commutes, ← AdjoinRoot.algebraMap_eq,
                      AlgHom.comp_algebraMap]))
                (algebraMap R (S ⧸ I.map (algebraMap R S)) x) = algebraMap R _ x from fun x => by
                  rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotientEquiv_apply,
                    RingHom.toFun_eq_coe, Ideal.quotientMap_mk, AlgEquiv.toRingEquiv_eq_coe,
                    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
                    Quotient.mk_algebraMap])).trans (AdjoinRoot.quotEquivQuotMap _ _)
#align power_basis.quotient_equiv_quotient_minpoly_map PowerBasis.quotientEquivQuotientMinpolyMap

structure on `AdjoinRoot f` is constructed.

We suggest stating results on `IsAdjoinRoot` instead of `AdjoinRoot` to achieve higher
generality, since `IsAdjoinRoot` works for all different constructions of `R[α]`
including `AdjoinRoot f = R[X]/(f)` itself.

## Main definitions and results