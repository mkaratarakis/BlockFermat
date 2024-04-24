def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.FG :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩
#align is_noetherian_def isNoetherian_def

def IsNoetherian.equivPUnitOfProdInjective (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} := by
  apply Nonempty.some
  obtain ⟨n, w⟩ :=
    IsNoetherian.disjoint_partialSups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
  specialize w n (le_refl n)
  apply Nonempty.intro
  -- Porting note: refine' makes this line time out at elaborator
  refine (LinearMap.tailingLinearEquiv f i n).symm ≪≫ₗ ?_
  rw [w]
  apply Submodule.botEquivPUnit
#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPUnitOfProdInjective

def IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R
#align is_noetherian_ring IsNoetherianRing

def
#align is_noetherian_ring_iff_ideal_fg isNoetherianRing_iff_ideal_fg