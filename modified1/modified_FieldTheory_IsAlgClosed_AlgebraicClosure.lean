def MonicIrreducible : Type u :=
  { f : k[X] // Monic f ∧ Irreducible f }
#align algebraic_closure.monic_irreducible AlgebraicClosure.MonicIrreducible

def evalXSelf (f : MonicIrreducible k) : MvPolynomial (MonicIrreducible k) k :=
  Polynomial.eval₂ MvPolynomial.C (X f) f
set_option linter.uppercaseLean3 false in
#align algebraic_closure.eval_X_self AlgebraicClosure.evalXSelf

def spanEval : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Ideal.span <| Set.range <| evalXSelf k
#align algebraic_closure.span_eval AlgebraicClosure.spanEval

def toSplittingField (s : Finset (MonicIrreducible k)) :
    MvPolynomial (MonicIrreducible k) k →ₐ[k] SplittingField (∏ x in s, x : k[X]) :=
  MvPolynomial.aeval fun f =>
    if hf : f ∈ s then
      rootOfSplits _
        ((splits_prod_iff _ fun (j : MonicIrreducible k) _ => j.2.2.ne_zero).1
          (SplittingField.splits _) f hf)
        (mt isUnit_iff_degree_eq_zero.2 f.2.2.not_unit)
    else 37
#align algebraic_closure.to_splitting_field AlgebraicClosure.toSplittingField

def maxIdeal : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Classical.choose <| Ideal.exists_le_maximal _ <| spanEval_ne_top k
#align algebraic_closure.max_ideal AlgebraicClosure.maxIdeal

def AdjoinMonic : Type u :=
  MvPolynomial (MonicIrreducible k) k ⧸ maxIdeal k
#align algebraic_closure.adjoin_monic AlgebraicClosure.AdjoinMonic

def toAdjoinMonic : k →+* AdjoinMonic k :=
  (Ideal.Quotient.mk _).comp C
#align algebraic_closure.to_adjoin_monic AlgebraicClosure.toAdjoinMonic

def stepAux (n : ℕ) : Σ α : Type u, Field α :=
  Nat.recOn n ⟨k, inferInstance⟩ fun _ ih => ⟨@AdjoinMonic ih.1 ih.2, @AdjoinMonic.field ih.1 ih.2⟩
#align algebraic_closure.step_aux AlgebraicClosure.stepAux

def Step (n : ℕ) : Type u :=
  (stepAux k n).1
#align algebraic_closure.step AlgebraicClosure.Step

def toStepZero : k →+* Step k 0 :=
  RingHom.id k
#align algebraic_closure.to_step_zero AlgebraicClosure.toStepZero

def toStepSucc (n : ℕ) : Step k n →+* (Step k (n + 1)) :=
  @toAdjoinMonic (Step k n) (Step.field k n)
#align algebraic_closure.to_step_succ AlgebraicClosure.toStepSucc

def toStepOfLE' (m n : ℕ) (h : m ≤ n) : Step k m → Step k n :=
Nat.leRecOn h @fun a => toStepSucc k a

private theorem toStepOfLE'.succ (m n : ℕ) (h : m ≤ n) :
    toStepOfLE' k m (Nat.succ n) (h.trans n.le_succ) =
    (toStepSucc k n) ∘ toStepOfLE' k m n h := by
  ext x
  convert Nat.leRecOn_succ h x
  exact h.trans n.le_succ

/-- The canonical ring homomorphism to a step with a greater index. -/
def toStepOfLE (m n : ℕ) (h : m ≤ n) : Step k m →+* Step k n where
  toFun := toStepOfLE' k m n h
  map_one' := by
-- Porting note: original proof was `induction' h with n h ih; · exact Nat.leRecOn_self 1`
--                                   `rw [Nat.leRecOn_succ h, ih, RingHom.map_one]`
    induction' h with a h ih
    · exact Nat.leRecOn_self 1
    · rw [toStepOfLE'.succ k m a h]; simp [ih]
  map_mul' x y := by
-- Porting note: original proof was `induction' h with n h ih; · simp_rw [Nat.leRecOn_self]`
--                                   `simp_rw [Nat.leRecOn_succ h, ih, RingHom.map_mul]`
    induction' h with a h ih
    · dsimp [toStepOfLE']; simp_rw [Nat.leRecOn_self]
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
-- Porting note: original proof was `induction' h with n h ih; · exact Nat.leRecOn_self 0`
--                                   `rw [Nat.leRecOn_succ h, ih, RingHom.map_zero]`
  map_zero' := by
    induction' h with a h ih
    · exact Nat.leRecOn_self 0
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
  map_add' x y := by
-- Porting note: original proof was `induction' h with n h ih; · simp_rw [Nat.leRecOn_self]`
--                                   `simp_rw [Nat.leRecOn_succ h, ih, RingHom.map_add]`
    induction' h with a h ih
    · dsimp [toStepOfLE']; simp_rw [Nat.leRecOn_self]
    · simp_rw [toStepOfLE'.succ k m a h]; simp only at ih; simp [ih]
#align algebraic_closure.to_step_of_le AlgebraicClosure.toStepOfLE

def AlgebraicClosureAux [Field k] : Type u :=
  Ring.DirectLimit (AlgebraicClosure.Step k) fun i j h => AlgebraicClosure.toStepOfLE k i j h
#align algebraic_closure AlgebraicClosureAux

def ofStep (n : ℕ) : Step k n →+* AlgebraicClosureAux k :=
  Ring.DirectLimit.of _ _ _
#noalign algebraic_closure.of_step

def

/-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
def ofStepHom (n) : Step k n →ₐ[k] AlgebraicClosureAux k :=
  { ofStep k n with
    commutes' := by
    -- Porting note: Originally `(fun x => Ring.DirectLimit.of_f n.zero_le x)`
    -- I think one problem was in recognizing that we want `toStepOfLE` in `of_f`
      intro x
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
      convert @Ring.DirectLimit.of_f ℕ _ (Step k) _ (fun m n h => (toStepOfLE k m n h : _ → _))
          0 n n.zero_le x }
#noalign algebraic_closure.of_step_hom

def AlgebraicClosure : Type u :=
  MvPolynomial (AlgebraicClosureAux k) k ⧸
    RingHom.ker (MvPolynomial.aeval (R := k) id).toRingHom

namespace AlgebraicClosure

instance instCommRing : CommRing (AlgebraicClosure k) := Ideal.Quotient.commRing _
instance instInhabited : Inhabited (AlgebraicClosure k) := ⟨37⟩

instance {S : Type*} [DistribSMul S k] [IsScalarTower S k k] : SMul S (AlgebraicClosure k) :=
  Submodule.Quotient.instSMul' _

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k) :=
  Ideal.Quotient.algebra _

instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Algebra S k] [Algebra R k]
    [IsScalarTower R S k] : IsScalarTower R S (AlgebraicClosure k) :=
  Ideal.Quotient.isScalarTower _ _ _

/-- The equivalence between `AlgebraicClosure` and `AlgebraicClosureAux`, which we use to transfer
properties of `AlgebraicClosureAux` to `AlgebraicClosure` -/
def algEquivAlgebraicClosureAux :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosureAux k := by
  delta AlgebraicClosure
  exact Ideal.quotientKerAlgEquivOfSurjective
    (fun x => ⟨MvPolynomial.X x, by simp⟩)

-- Those two instances are copy-pasta from the analogous instances for `SplittingField`
instance instGroupWithZero : GroupWithZero (AlgebraicClosure k) :=
  let e := algEquivAlgebraicClosureAux k
  { inv := fun a ↦ e.symm (e a)⁻¹
    inv_zero := by simp
    mul_inv_cancel := fun a ha ↦ e.injective $ by simp [(AddEquivClass.map_ne_zero_iff _).2 ha]
    __ := e.surjective.nontrivial }

instance instField : Field (AlgebraicClosure k) where
  __ := instCommRing _
  __ := instGroupWithZero _
  ratCast q := algebraMap k _ q
  ratCast_def q := by
    change algebraMap k _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  qsmul := (· • ·)
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' $ by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

instance isAlgClosed : IsAlgClosed (AlgebraicClosure k) :=
  IsAlgClosed.of_ringEquiv _ _ (algEquivAlgebraicClosureAux k).symm.toRingEquiv
#align algebraic_closure.is_alg_closed AlgebraicClosure.isAlgClosed