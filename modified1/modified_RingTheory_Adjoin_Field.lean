def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type*} [CommRing R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm <| AlgEquiv.ofBijective (Minpoly.toAdjoin F x) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun P₁ hP₁ ↦ ?_, Minpoly.toAdjoin.surjective F x⟩
    obtain ⟨P, rfl⟩ := mk_surjective P₁
    refine AdjoinRoot.mk_eq_zero.mpr (minpoly.dvd F x ?_)
    rwa [Minpoly.toAdjoin_apply', liftHom_mk, ← Subalgebra.coe_eq_zero, aeval_subalgebra_coe] at hP₁
#align alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly

def Algebra.adjoin.liftSingleton {S T : Type*}
    [CommRing S] [CommRing T] [Algebra F S] [Algebra F T]
    (x : S) (y : T) (h : aeval y (minpoly F x) = 0) :
    Algebra.adjoin F {x} →ₐ[F] T :=
  (AdjoinRoot.liftHom _ y h).comp (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F x).toAlgHom

open Finset

/-- If `K` and `L` are field extensions of `F` and we have `s : Finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `Algebra.adjoin F s` embeds in `L`. -/
theorem Polynomial.lift_of_splits {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] (s : Finset K) : (∀ x ∈ s, IsIntegral F x ∧
      Splits (algebraMap F L) (minpoly F x)) → Nonempty (Algebra.adjoin F (s : Set K) →ₐ[F] L) := by
  classical
    refine Finset.induction_on s (fun _ ↦ ?_) fun a s _ ih H ↦ ?_
    · rw [coe_empty, Algebra.adjoin_empty]
      exact ⟨(Algebra.ofId F L).comp (Algebra.botEquiv F K)⟩
    rw [forall_mem_insert] at H
    rcases H with ⟨⟨H1, H2⟩, H3⟩
    cases' ih H3 with f
    choose H3 _ using H3
    rw [coe_insert, Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin]
    set Ks := Algebra.adjoin F (s : Set K)
    haveI : FiniteDimensional F Ks := ((Submodule.fg_iff_finiteDimensional _).1
      (fg_adjoin_of_finite s.finite_toSet H3)).of_subalgebra_toSubmodule
    letI := fieldOfFiniteDimensional F Ks
    letI := (f : Ks →+* L).toAlgebra
    have H5 : IsIntegral Ks a := H1.tower_top
    have H6 : (minpoly Ks a).Splits (algebraMap Ks L) := by
      refine splits_of_splits_of_dvd _ ((minpoly.monic H1).map (algebraMap F Ks)).ne_zero
        ((splits_map_iff _ _).2 ?_) (minpoly.dvd _ _ ?_)
      · rw [← IsScalarTower.algebraMap_eq]
        exact H2
      · rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨y, hy⟩ := Polynomial.exists_root_of_splits _ H6 (minpoly.degree_pos H5).ne'
    exact ⟨Subalgebra.ofRestrictScalars F _ <| Algebra.adjoin.liftSingleton Ks a y hy⟩
#align lift_of_splits Polynomial.lift_of_splits