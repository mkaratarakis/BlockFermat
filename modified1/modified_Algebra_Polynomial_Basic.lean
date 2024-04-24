def add : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {R : Type u} [Ring R] : R[X] → R[X]
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance zero : Zero R[X] :=
  ⟨⟨0⟩⟩
#align polynomial.has_zero Polynomial.zero

def toFinsuppIso : R[X] ≃+* R[ℕ] where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv := fun ⟨_p⟩ => rfl
  right_inv _p := rfl
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add
#align polynomial.to_finsupp_iso Polynomial.toFinsuppIso

def support : R[X] → Finset ℕ
  | ⟨p⟩ => p.support
#align polynomial.support Polynomial.support

def monomial (n : ℕ) : R →ₗ[R] R[X] where
  toFun t := ⟨Finsupp.single n t⟩
  -- porting note (#10745): was `simp`.

def C : R →+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }
#align polynomial.C Polynomial.C

def X : R[X] :=
  monomial 1 1
#align polynomial.X Polynomial.X

def coeff : R[X] → ℕ → R
  | ⟨p⟩ => p
#align polynomial.coeff Polynomial.coeff

def sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) : S :=
  ∑ n in p.support, f n (p.coeff n)
#align polynomial.sum Polynomial.sum

def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) :
    p.sum f = ∑ n in p.support, f n (p.coeff n) :=
  rfl
#align polynomial.sum_def Polynomial.sum_def

def p q]
  exact Finsupp.sum_add_index (fun i _ ↦ hf i) (fun a _ b₁ b₂ ↦ h_add a b₁ b₂)
#align polynomial.sum_add_index Polynomial.sum_add_index

def erase (n : ℕ) : R[X] → R[X]
  | ⟨p⟩ => ⟨p.erase n⟩
#align polynomial.erase Polynomial.erase

def update (p : R[X]) (n : ℕ) (a : R) : R[X] :=
  Polynomial.ofFinsupp (p.toFinsupp.update n a)
#align polynomial.update Polynomial.update

structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `AddMonoidAlgebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `R[X]` and `R[ℕ]` is
done through `ofFinsupp` and `toFinsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `R[ℕ]`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `Polynomial.toFinsuppIso`. These should
in general not be used once the basic API for polynomials is constructed.
-/


set_option linter.uppercaseLean3 false

noncomputable section

/-- `Polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ
#align polynomial Polynomial

structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {R : Type u} [Ring R] : R[X] → R[X]
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance zero : Zero R[X] :=
  ⟨⟨0⟩⟩
#align polynomial.has_zero Polynomial.zero