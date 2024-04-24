def botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v+1} where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl
#align submodule.bot_equiv_punit Submodule.botEquivPUnit

def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun x := x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
#align submodule.top_equiv Submodule.topEquiv

def {p p' : Submodule R M} : Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : M) :=
  disjoint_iff_inf_le.trans <| show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by simp
#align submodule.disjoint_def Submodule.disjoint_def

def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule ℕ M where
  toFun S := { S with smul_mem' := fun r s hs ↦ show r • s ∈ S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align add_submonoid.to_nat_submodule AddSubmonoid.toNatSubmodule

def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M where
  toFun S := { S with smul_mem' := fun _ _ hs ↦ S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align add_subgroup.to_int_submodule AddSubgroup.toIntSubmodule

structure on `Submodule`s

This file defines the lattice structure on submodules, `Submodule.CompleteLattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.

Many results about operations on this lattice structure are defined in `LinearAlgebra/Basic.lean`,
most notably those which use `span`.

## Implementation notes

structure should match the `AddSubmonoid.CompleteLattice` structure, and we should try
to unify the APIs where possible.

-/

universe v

variable {R S M : Type*}

section AddCommMonoid

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMul S R] [IsScalarTower S R M]
variable {p q : Submodule R M}

namespace Submodule

/-!
## Bottom element of a submodule