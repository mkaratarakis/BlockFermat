def Iso (X Y : Submodule R M × Submodule R M) : Prop :=
  Nonempty <| (X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.subtype

theorem iso_symm {X Y : Submodule R M × Submodule R M} : Iso X Y → Iso Y X :=
  fun ⟨f⟩ => ⟨f.symm⟩

theorem iso_trans {X Y Z : Submodule R M × Submodule R M} : Iso X Y → Iso Y Z → Iso X Z :=
  fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

@[nolint unusedArguments]
theorem second_iso {X Y : Submodule R M} (_ : X ⋖ X ⊔ Y) :
    Iso (X,X ⊔ Y) (X ⊓ Y,Y) := by
  constructor
  rw [sup_comm, inf_comm]
  dsimp
  exact (LinearMap.quotientInfEquivSupQuotient Y X).symm

instance instJordanHolderLattice : JordanHolderLattice (Submodule R M) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := inf_covBy_of_covBy_sup_of_covBy_sup_left
  Iso := Iso
  iso_symm := iso_symm
  iso_trans := iso_trans
  second_iso := second_iso
#align jordan_holder_module JordanHolderModule.instJordanHolderLattice

structure on the endomorphism ring of a simple module.

## Main Results

structure on the endomorphism ring.
  * `isSimpleModule_iff_quot_maximal`:
    a module is simple iff it's isomorphic to the quotient of the ring by a maximal left ideal.
  * `sSup_simples_eq_top_iff_isSemisimpleModule`:
    a module is semisimple iff it is generated by its simple submodules.
  * `IsSemisimpleModule.annihilator_isRadical`:
    the annihilator of a semisimple module over a commutative ring is a radical ideal.
  * `IsSemisimpleModule.submodule`, `IsSemisimpleModule.quotient`:
    any submodule or quotient module of a semisimple module is semisimple.
  * `isSemisimpleModule_of_isSemisimpleModule_submodule`:
    a module generated by semisimple submodules is itself semisimple.
  * `IsSemisimpleRing.isSemisimpleModule`: every module over a semisimple ring is semisimple.
  * `instIsSemisimpleRingForAllRing`: a finite product of semisimple rings is semisimple.
  * `RingHom.isSemisimpleRing_of_surjective`: any quotient of a semisimple ring is semisimple.

## TODO