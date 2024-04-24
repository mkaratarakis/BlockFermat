def [Small.{w,v} M] :
    Module.Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) :=
  ⟨fun h =>
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩,
    fun h => ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩⟩
#align module.free_def Module.free_def

def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩
#align module.free.of_basis Module.Free.of_basis

def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose
#align module.free.choose_basis_index Module.Free.ChooseBasisIndex

def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some
#align module.free.choose_basis Module.Free.chooseBasis

def repr : M ≃ₗ[R] ChooseBasisIndex R M →₀ R :=
  (chooseBasis R M).repr
#align module.free.repr Module.Free.repr

def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S
#align module.free.constr Module.Free.constr

structure provided by `Semiring.toModule` is free. -/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)
#align module.free.self Module.Free.self