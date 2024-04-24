def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020):
-- deriving Group, Fintype
#align polynomial.gal Polynomial.Gal

def uniqueGalOfSplits (h : p.Splits (RingHom.id F)) : Unique p.Gal where
  default := 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
#align polynomial.gal.unique_gal_of_splits Polynomial.Gal.uniqueGalOfSplits

def restrict [Fact (p.Splits (algebraMap F E))] : (E ≃ₐ[F] E) →* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField
#align polynomial.gal.restrict Polynomial.Gal.restrict

def mapRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField → rootSet p E :=
  Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ <| rootSet_mapsTo _
#align polynomial.gal.map_roots Polynomial.Gal.mapRoots

def rootsEquivRoots [Fact (p.Splits (algebraMap F E))] : rootSet p p.SplittingField ≃ rootSet p E :=
  Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)
#align polynomial.gal.roots_equiv_roots Polynomial.Gal.rootsEquivRoots

def [Fact (p.Splits (algebraMap F E))] (ϕ : p.Gal) (x : rootSet p E) :
    ϕ • x = rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x) :=
  rfl

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance galAction [Fact (p.Splits (algebraMap F E))] : MulAction p.Gal (rootSet p E) where
  one_smul _ := by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply, mul_smul]
#align polynomial.gal.gal_action Polynomial.Gal.galAction

def galActionHom [Fact (p.Splits (algebraMap F E))] : p.Gal →* Equiv.Perm (rootSet p E) :=
  MulAction.toPermHom _ _
#align polynomial.gal.gal_action_hom Polynomial.Gal.galActionHom

def restrictDvd (hpq : p ∣ q) : q.Gal →* p.Gal :=
  haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q) hpq⟩
#align polynomial.gal.restrict_dvd Polynomial.Gal.restrictDvd

def [Decidable (q = 0)] (hpq : p ∣ q) :
    restrictDvd hpq =
      if hq : q = 0 then 1
      else
        @restrict F _ p _ _ _
          ⟨splits_of_splits_of_dvd (algebraMap F q.SplittingField) hq (SplittingField.splits q)
              hpq⟩ := by
  -- Porting note: added `unfold`
  unfold restrictDvd
  convert rfl
#align polynomial.gal.restrict_dvd_def Polynomial.Gal.restrictDvd_def

def restrictProd : (p * q).Gal →* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))
#align polynomial.gal.restrict_prod Polynomial.Gal.restrictProd

def restrictComp (hq : q.natDegree ≠ 0) : (p.comp q).Gal →* p.Gal :=
  let h : Fact (Splits (algebraMap F (p.comp q).SplittingField) p) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h
#align polynomial.gal.restrict_comp Polynomial.Gal.restrictComp