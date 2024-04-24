def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Splits (algebraMap K F) f) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.Splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f];
    exact Classical.choice (lift_of_splits _ fun y hy =>
      have : aeval y f = 0 := (eval₂_eq_eval_map _).trans <|
        (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
    ⟨IsAlgebraic.isIntegral ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf <| minpoly.dvd _ _ this⟩)) Algebra.toTop
#align polynomial.is_splitting_field.lift Polynomial.IsSplittingField.lift