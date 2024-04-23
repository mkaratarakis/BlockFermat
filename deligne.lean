
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

namespace LocalRing

variable {A B: Type _} [CommRing B] [CommRing A] [LocalRing A] [LocalRing B]
  [Algebra A B] [IsLocalRingHom (algebraMap A B)]

/-- A local ring automorphism is local. -/
instance (e : B ≃+* B) :
    IsLocalRingHom e.toRingHom where
  map_nonunit := by sorry

noncomputable instance generalAlgebraMap :
    Algebra (LocalRing.ResidueField A) (LocalRing.ResidueField B) := sorry

/-- The group homomorphism from the Galois group to the Galois group of residue fields. -/
noncomputable def algebraEquivToResidueEquiv :
    (B ≃ₐ[A] B) →* LocalRing.ResidueField B ≃ₐ[LocalRing.ResidueField A] LocalRing.ResidueField B
    where
  toFun x :=
    { toFun := LocalRing.ResidueField.map x.toRingEquiv.toRingHom
      invFun := LocalRing.ResidueField.map x.symm.toRingEquiv.toRingHom
      left_inv := sorry
      right_inv := sorry
      map_mul' := sorry
      map_add' := sorry
      commutes' := by sorry
       }
  map_one' := sorry
  map_mul' x y := sorry

end LocalRing

namespace ValuationSubring

variable {K L : Type _} [Field K] [Field L]

/-- The map from the pullback of a valuation subring A to A along a ring homomorphism K →+* L -/
def RingHom.valuationSubringComap (A : ValuationSubring L) (f : K →+* L) : comap A f →+* A
    where
  toFun x := ⟨f x.1, x.2⟩
  map_one' := sorry
  map_mul' x y := sorry
  map_add' x y := sorry
  map_zero' := sorry

section
--
variable (K) [Field K] [Algebra K L]

open scoped Pointwise

/-- The group homomorphism from the decomposition group to the group
 of automorphisms of the residue field of a valuation subring A-/
def decompositionSubgroupToResidueAut (A : ValuationSubring L) :
    A.decompositionSubgroup K →* RingAut (LocalRing.ResidueField A) :=
  LocalRing.ResidueField.mapAut.comp (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A)

instance AlgebraComap(A : ValuationSubring L) : Algebra (comap A (algebraMap K L)) A := sorry

/-- The group homomorphism from the decomposition group to the Galois group of
A fixing the pullback of A. -/
def decompositionSubgroup.restrict (A : ValuationSubring L) :
    A.decompositionSubgroup K →* A ≃ₐ[comap A (algebraMap K L)] A
    where
  toFun x :=
    { MulSemiringAction.toRingAut (A.decompositionSubgroup K) A x with
      commutes' := sorry
    }
  map_one' := by sorry
  map_mul' := by sorry

theorem ComapNeTopOfAlgebraic (v : ValuationSubring L) (h : v ≠ ⊤)
    (ha : Algebra.IsAlgebraic K L) : v.comap (algebraMap K L) ≠ ⊤ := sorry

end

namespace frobenius

variable [Fintype K] [Algebra K L]

variable (K) (L)

def frob : L →ₐ[K] L
 where
  toFun x := x ^ Fintype.card K
  map_one' := sorry
  map_mul' x y := sorry
  map_zero' := sorry
  map_add' x y := sorry
  commutes' x := sorry

variable {K} {L}

theorem frob_bijective (ha : Algebra.IsAlgebraic K L) : Function.Bijective (frob K L) := sorry

noncomputable def equiv (ha : Algebra.IsAlgebraic K L) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (frob K L) (frob_bijective ha)

end frobenius

open scoped NumberField

variable [NumberField K] [Algebra K L] [IsGalois K L] (K)

/-- The natural reduction homomorphism from the decomposition group
  to the Galois group of the residue field of A
  fixing the residue field of the pullback of A -/
noncomputable def decompositionSubgroup.toResidueFieldEquiv (A : ValuationSubring L) :
    decompositionSubgroup K A →*
      LocalRing.ResidueField A ≃ₐ[LocalRing.ResidueField (comap A (algebraMap K L))]
        LocalRing.ResidueField A := LocalRing.algebraEquivToResidueEquiv.comp (decompositionSubgroup.restrict K A)

/-- The natural reduction homomorphism is surjective. -/
theorem decompositionSubgroup.surjective (v : ValuationSubring L) :
    Function.Surjective (decompositionSubgroup.toResidueFieldEquiv K v) := sorry

/-- If the inertia subgroup is trivial, the natural reduction homomorphism is bijective. -/
theorem decompositionSubgroup.bijective (v : ValuationSubring L) (h : inertiaSubgroup K v = ⊥) :
    Function.Bijective (decompositionSubgroup.toResidueFieldEquiv K v) := sorry

theorem algebraComapAlgebraic (B : ValuationSubring L) :
    Algebra.IsAlgebraic (LocalRing.ResidueField (B.comap (algebraMap K L)))
      (LocalRing.ResidueField B) := sorry

variable [NumberField L]

theorem subset_of_val_subring (B : ValuationSubring L) : (𝓞 L).toSubring ≤ B.toSubring :=
  sorry

/-- The map (𝓞 L) →+* local_ring.residue_field B -/
def RingOfIntToRes (B : ValuationSubring L) : 𝓞 L →+* LocalRing.ResidueField B :=
  (LocalRing.residue B).comp (Subring.inclusion (subset_of_val_subring B))

/-- The map (𝓞 L) →+* local_ring.residue_field B is surjective-/
theorem RingOfIntToResSurj (B : ValuationSubring L) (htop : B ≠ ⊤) :
  Function.Surjective (RingOfIntToRes B) := sorry

/-- The isomorphism  (𝓞 L) ⧸ (ring_of_int_to_res B).ker
   ≃+* local_ring.residue_field B -/
noncomputable def resFieldEquiv (B : ValuationSubring L) (htop : B ≠ ⊤) :
    𝓞 L ⧸ RingHom.ker (RingOfIntToRes B) ≃+* LocalRing.ResidueField B :=
  RingHom.quotientKerEquivOfSurjective (RingOfIntToResSurj B htop)

theorem fintypeOfNeBot (B : ValuationSubring K) (htop : B ≠ ⊤) :
    Fintype (LocalRing.ResidueField B) := sorry

/-- The Frobenius element as an element of the decomposition group defined
 as a random pre-image. -/
noncomputable def Frob (K L : Type _) [Field K] [Field L] [NumberField K] [Algebra K L]
    [IsGalois K L] (v : ValuationSubring L) (hv : v ≠ ⊤) : decompositionSubgroup K v :=
  by
  letI :=
    fintypeOfNeBot K (v.comap (algebraMap K L))
      (ComapNeTopOfAlgebraic K v hv Normal.isAlgebraic')
  have := decompositionSubgroup.surjective K v
  let f :
    LocalRing.ResidueField v ≃ₐ[LocalRing.ResidueField (v.comap (algebraMap K L))]
      LocalRing.ResidueField v := frobenius.equiv (algebraComapAlgebraic K v)
  specialize this f
  exact this.choose

end ValuationSubring


variable (k : Type _) [CommRing k] [TopologicalSpace k] [TopologicalRing k]

/-- `galois_rep k` is the type of 2-dimensional Galois representations where `k` is a
topological ring defined as the continuous monoid homomorphism of the absolute Galois group
of the rationals to the `GL_2 k`-/
def GaloisRep :=
  ContinuousMonoidHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (GL (Fin 2) k)

variable {k}

open ValuationSubring

/-- `is_unramified ρ q` if the inertia subgroup is contained in its kernel -/
noncomputable def IsUnramified (ρ : GaloisRep k) (q : ValuationSubring (AlgebraicClosure ℚ)) : Prop :=
  inertiaSubgroup ℚ q ≤ ρ.toMonoidHom.ker.subgroupOf (decompositionSubgroup ℚ q)

open scoped BigOperators

open Polynomial Nat AlgebraicClosure

variable {K L : Type _} [Field K] [Field L] {p : ℕ} [Fact (Nat.Prime p)] [Algebra K L]

/-- A Dirichlet character is defined as a monoid homomorphism which is periodic. -/
abbrev DirChar (R : Type _) [Monoid R] (n : ℕ) := Units (ZMod n) →* Units R

/-- The map from the algebraic closure for K to L when L is algebraically closed -/
noncomputable def functoriality (_ : IsAlgClosed L) : AlgebraicClosure K →+* L :=
  AlgHom.toRingHom (IsAlgClosed.lift (isAlgebraic K))

/-- An arbitrary fixed map from the algebraic closure of ℚ into ℂ -/
noncomputable def algClosRatToComplex : AlgebraicClosure ℚ →+* ℂ :=
  functoriality Complex.isAlgClosed

/-- An arbitrary fixed map from algebraic closure of ℚ into alg closure of ℚ_p. -/
noncomputable def algClosRatToPAdic (p : ℕ) [Fact (Nat.Prime p)] :
    AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[p] :=
    functoriality (isAlgClosed ℚ_[p])

def ZMod.Unit.mk {N : ℕ} {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ N) : (ZMod N)ˣ
    where
  val := q
  inv := q⁻¹
  val_inv := sorry
  inv_val := by sorry

/-- The Hecke operator -/
noncomputable def heckeOperator {N : ℕ} {k : ℕ} {q : ℕ} (f : ModularForm (Gamma1 N) k)
    (h : Nat.Prime q) (χ : DirChar ℂ N) (hqN : ¬q ∣ N) (z : UpperHalfPlane) : ℂ :=
  ∑ n in Finset.range q,
      f
        ⟨(z + n) / q,
          sorry
          ⟩ +
      χ (ZMod.Unit.mk h hqN) * q ^ (k - 1) * f
        ⟨q * z, sorry⟩

/-- Only asking that it is an eigenvector for the good primes. -/
def IsWeakEigenform {N : ℕ} {k : ℕ} (f : ModularForm (Gamma1 N) k) (χ : DirChar ℂ N) :
    Prop :=
  f ≠ 0 ∧
    ∀ {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ N),
      ∃ a : ℂ, ∀ z : UpperHalfPlane, heckeOperator f h χ hqN z = a * f z

/-- An eigenvalue of the Hecke operator. -/
noncomputable def eigenvalue {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} (hqN : ¬q ∣ N) {χ : DirChar ℂ N}
    (hf : IsWeakEigenform f χ) : ℂ :=
  Exists.choose (hf.2 h hqN)

/--The eigenvalues of the Hecke operator are algebraic. -/
theorem EigenvaluesAlgebraic {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} (hqN : ¬q ∣ N) {χ : DirChar ℂ N}
    (hf : IsWeakEigenform f χ) :
    ∃ a : AlgebraicClosure ℚ, algClosRatToComplex a = eigenvalue h hqN hf := sorry

/-- The algebraic eigenvalue of the Hecke operator -/
noncomputable def AlgEigenvalue {N : ℕ} {k : ℕ} {q : ℕ} (h : Nat.Prime q)
    {f : ModularForm (Gamma1 N) k} {χ : DirChar ℂ N} (hf : IsWeakEigenform f χ)
    (hqN : ¬q ∣ N) : AlgebraicClosure ℚ :=
  Exists.choose (EigenvaluesAlgebraic h hqN hf)

theorem NonnunitPrimesInComap (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤) :
    ∃ q : ℕ, Nat.Prime q ∧ ↑q ∈ LocalRing.maximalIdeal (v.comap (algebraMap ℚ (AlgebraicClosure ℚ))) :=
  sorry

noncomputable def q (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤) : ℕ :=
  Exists.choose (NonnunitPrimesInComap v h)

theorem q.isPrime {v : ValuationSubring (AlgebraicClosure ℚ)} (h : v ≠ ⊤) :
    Nat.Prime (q v h) := sorry

def ZMod.Unit {N : ℕ} {q : ℕ} (h : Nat.Prime q) (hqN : ¬q ∣ p * N) : (ZMod N)ˣ
    where
  val := q
  inv := q⁻¹
  val_inv := sorry
  inv_val := sorry

theorem div (N : ℕ) (v : ValuationSubring (AlgebraicClosure ℚ)) (h : v ≠ ⊤)
    (hqpN : ¬q v h ∣ p * N) : ¬q v h ∣ N := sorry

section

variable (R : Type _) [CommRing R] [TopologicalSpace R] [TopologicalRing R] [NumberField K]
  [Algebra K L] [IsGalois K L]

open ValuationSubring

variable {R}

instance AlgebraicClosureNormedField : NormedField (AlgebraicClosure ℚ_[p]) :=sorry

/-- Units (ZMod n) →* Units ℂ -/
noncomputable def DirCharComplex {N : ℕ} (χ : DirChar (AlgebraicClosure ℚ) N) :
    DirChar ℂ N := (Units.map algClosRatToComplex.toMonoidHom).comp χ

/-- Units (ZMod n) →* Units ℚ_[p] -/
noncomputable def DirCharAlgClosRat {N : ℕ} {p : ℕ} [Fact (Nat.Prime p)]
    (χ : DirChar (AlgebraicClosure ℚ) N) :
    DirChar (AlgebraicClosure ℚ_[p]) N :=
  (Units.map (algClosRatToPAdic p).toMonoidHom).comp χ

instance : IsGalois ℚ (AlgebraicClosure ℚ) := sorry

theorem Deligne {N : ℕ} {k : ℕ} {f : ModularForm (Gamma1 N) k} (χ : DirChar (AlgebraicClosure ℚ) N)
   (hf : IsWeakEigenform f (DirCharComplex χ)) :
    ∃ (ρ : GaloisRep (AlgebraicClosure ℚ_[p])),
      ∀ (v : ValuationSubring (AlgebraicClosure ℚ)) (hv : v ≠ ⊤) (hqpN : ¬ q v hv ∣ p * N), (IsUnramified ρ v)
    ∧ let a := C ((algClosRatToPAdic p) (AlgEigenvalue (q.isPrime hv) hf (div N v hv hqpN)))
    let χq  := (Units.coeHom (AlgebraicClosure ℚ_[p])).comp (DirCharAlgClosRat χ) (ZMod.Unit (q.isPrime hv) hqpN)
Matrix.charpoly (Matrix.of (ρ.toMonoidHom (Frob ℚ (AlgebraicClosure ℚ) v hv))) =
X ^ 2 - (a * X) + ((q v hv) ^ (k - 1) : (AlgebraicClosure ℚ_[p])[X]) * (C χq) := sorry

end
