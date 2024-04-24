def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  carrier := s
  zero_mem' := by simpa [hs] using p.zero_mem'
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'
#align submodule.copy Submodule.copy

def toModule' (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) :
    Module R' s :=
  haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

-- Porting note: removing `@[simp]` since it can already be proven
theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
#align submodule.mem_carrier Submodule.mem_carrier

def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl
#align submodule.vadd_def Submodule.vadd_def

def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }
#align submodule.to_add_subgroup Submodule.toAddSubgroup

structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] extends
  AddSubmonoid M, SubMulAction R M : Type v
#align submodule Submodule

structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

-- Porting note: removing `@[simp]` since it can already be proven
theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
#align submodule.mem_carrier Submodule.mem_carrier

structure eta
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl
#align submodule.coe_mk Submodule.coe_mk