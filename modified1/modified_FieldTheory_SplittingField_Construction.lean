def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else X
#align polynomial.factor Polynomial.factor

def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))
#align polynomial.remove_factor Polynomial.removeFactor

def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], K[X] →
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩
#align polynomial.splitting_field_aux_aux Polynomial.SplittingFieldAuxAux

def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1
#align polynomial.splitting_field_aux Polynomial.SplittingFieldAux

def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
#align polynomial.splitting_field Polynomial.SplittingField

def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩
#align polynomial.splitting_field.alg_equiv_splitting_field_aux Polynomial.SplittingField.algEquivSplittingFieldAux

def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  qsmul := (· • ·)
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' $ by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance instCharP (p : ℕ) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p

instance instExpChar (p : ℕ) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `SplittingField f`.
example :
    (AddCommMonoid.natModule : Module ℕ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example :
    (AddCommGroup.intModule _ : Module ℤ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example [CharZero K] : SplittingField.algebra' f = algebraRat :=
  rfl

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField

def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb
#align polynomial.splitting_field.lift Polynomial.SplittingField.lift

def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f) <|
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1
#align polynomial.is_splitting_field.alg_equiv Polynomial.IsSplittingField.algEquiv

structure on `SplittingField f`.
example :
    (AddCommMonoid.natModule : Module ℕ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example :
    (AddCommGroup.intModule _ : Module ℤ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.algebra' f) :=
  rfl

example [CharZero K] : SplittingField.algebra' f = algebraRat :=
  rfl

example {q : ℚ[X]} : algebraInt (SplittingField q) = SplittingField.algebra' q :=
  rfl

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm
#align polynomial.is_splitting_field.splitting_field Polynomial.IsSplittingField.splittingField