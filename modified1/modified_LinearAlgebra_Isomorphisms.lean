def quotKerEquivRange : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  (LinearEquiv.ofInjective (f.ker.liftQ f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (LinearMap.ker f))).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)
#align linear_map.quot_ker_equiv_range LinearMap.quotKerEquivRange

def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans (LinearEquiv.ofTop (LinearMap.range f) (LinearMap.range_eq_top.2 hf))
#align linear_map.quot_ker_equiv_of_surjective LinearMap.quotKerEquivOfSurjective

def subToSupQuotient (p p' : Submodule R M) :
    { x // x ∈ p } →ₗ[R] { x // x ∈ p ⊔ p' } ⧸ comap (Submodule.subtype (p ⊔ p')) p' :=
  (comap (p ⊔ p').subtype p').mkQ.comp (Submodule.inclusion le_sup_left)

-- Porting note: breaking up original definition of quotientInfToSupQuotient to avoid timing out
theorem comap_leq_ker_subToSupQuotient (p p' : Submodule R M) :
    comap (Submodule.subtype p) (p ⊓ p') ≤ ker (subToSupQuotient p p') := by
  rw [LinearMap.ker_comp, Submodule.inclusion, comap_codRestrict, ker_mkQ, map_comap_subtype]
  exact comap_mono (inf_le_inf_right _ le_sup_left)

/-- Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotientInfToSupQuotient (p p' : Submodule R M) :
    (↥p) ⧸ (comap p.subtype (p ⊓ p')) →ₗ[R] (↥(p ⊔ p')) ⧸ (comap (p ⊔ p').subtype p') :=
   (comap p.subtype (p ⊓ p')).liftQ (subToSupQuotient p p') (comap_leq_ker_subToSupQuotient p p')
#align linear_map.quotient_inf_to_sup_quotient LinearMap.quotientInfToSupQuotient

def quotientInfEquivSupQuotient (p p' : Submodule R M) :
    (p ⧸ comap p.subtype (p ⊓ p')) ≃ₗ[R] _ ⧸ comap (p ⊔ p').subtype p' :=
  LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    ⟨quotientInfEquivSupQuotient_injective p p', quotientInfEquivSupQuotient_surjective p p'⟩
#align linear_map.quotient_inf_equiv_sup_quotient LinearMap.quotientInfEquivSupQuotient

def quotientQuotientEquivQuotientAux (h : S ≤ T) : (M ⧸ S) ⧸ T.map S.mkQ →ₗ[R] M ⧸ T :=
  liftQ _ (mapQ S T LinearMap.id h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker, mkQ_apply, mapQ_apply]
      exact (Quotient.mk_eq_zero _).mpr hx)
#align submodule.quotient_quotient_equiv_quotient_aux Submodule.quotientQuotientEquivQuotientAux

def quotientQuotientEquivQuotient : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
  { quotientQuotientEquivQuotientAux S T h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Quotient.inductionOn' x fun x => Quotient.inductionOn' x fun x => by simp
    right_inv := fun x => Quotient.inductionOn' x fun x => by simp }
#align submodule.quotient_quotient_equiv_quotient Submodule.quotientQuotientEquivQuotient