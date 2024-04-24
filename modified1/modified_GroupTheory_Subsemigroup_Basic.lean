def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'
#align subsemigroup.copy Subsemigroup.copy

def closure (s : Set M) : Subsemigroup M :=
  sInf { S | s ⊆ S }
#align subsemigroup.closure Subsemigroup.closure

def gi : GaloisInsertion (@closure M _) SetLike.coe :=
  GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure
#align subsemigroup.gi Subsemigroup.gi

def eqLocus (f g : M →ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]
#align mul_hom.eq_mlocus MulHom.eqLocus

def ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) :
    M →ₙ* N where
  toFun := f
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) x
#align mul_hom.of_mdense MulHom.ofDense

structure

This file defines bundled multiplicative and additive subsemigroups. We also define
a `CompleteLattice` structure on `Subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

structure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
#align mul_mem_class MulMemClass

structure satisfying `AddMemClass` is closed under addition. -/
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s
#align add_mem_class AddMemClass

structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
#align subsemigroup Subsemigroup

structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
#align add_subsemigroup AddSubsemigroup