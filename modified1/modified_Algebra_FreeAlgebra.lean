def hasCoeGenerator : Coe X (Pre R X) := ⟨of⟩
#align free_algebra.pre.has_coe_generator FreeAlgebra.Pre.hasCoeGenerator

def hasCoeSemiring : Coe R (Pre R X) := ⟨ofScalar⟩
#align free_algebra.pre.has_coe_semiring FreeAlgebra.Pre.hasCoeSemiring

def hasMul : Mul (Pre R X) := ⟨mul⟩
#align free_algebra.pre.has_mul FreeAlgebra.Pre.hasMul

def hasAdd : Add (Pre R X) := ⟨add⟩
#align free_algebra.pre.has_add FreeAlgebra.Pre.hasAdd

def hasZero : Zero (Pre R X) := ⟨ofScalar 0⟩
#align free_algebra.pre.has_zero FreeAlgebra.Pre.hasZero

def hasOne : One (Pre R X) := ⟨ofScalar 1⟩
#align free_algebra.pre.has_one FreeAlgebra.Pre.hasOne

def hasSMul : SMul R (Pre R X) := ⟨fun r m ↦ mul (ofScalar r) m⟩
#align free_algebra.pre.has_smul FreeAlgebra.Pre.hasSMul

def liftFun {A : Type*} [Semiring A] [Algebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .ofScalar c => algebraMap _ _ c
#align free_algebra.lift_fun FreeAlgebra.liftFun

def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)
#align free_algebra FreeAlgebra

def ι : X → FreeAlgebra R X := fun m ↦ Quot.mk _ m
#align free_algebra.ι FreeAlgebra.ι

def liftAux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h ↦ by
      induction' h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      · change algebraMap _ _ _ + liftFun R X f _ = liftFun R X f _
        simp
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
      · change algebraMap _ _ _ * liftFun R X f _ = liftFun R X f _
        simp
      · change liftFun R X f _ * algebraMap _ _ _ = liftFun R X f _
        simp
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
      repeat
        change liftFun R X f _ + liftFun R X f _ = _
        simp only [*]
        rfl
      repeat
        change liftFun R X f _ * liftFun R X f _ = _
        simp only [*]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    dsimp
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by tauto
-- Porting note: removed #align declaration since it is a private lemma

def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F ↦ F ∘ ι R
    left_inv := fun f ↦ by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F ↦ by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        simp only [Function.comp_apply, ι_def]
      | ofScalar x =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F _]
      | add a b ha hb =>
        -- Porting note: it is necessary to declare fa and fb explicitly otherwise Lean refuses
        -- to consider `Quot.mk (Rel R X) ·` as element of FreeAlgebra R X
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa + fb) = F (fa + fb)
        rw [AlgHom.map_add, AlgHom.map_add, ha, hb]
      | mul a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa * fb) = F (fa * fb)
        rw [AlgHom.map_mul, AlgHom.map_mul, ha, hb] }
#align free_algebra.lift FreeAlgebra.lift

def equivMonoidAlgebraFreeMonoid :
    FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  AlgEquiv.ofAlgHom (lift R fun x ↦ (MonoidAlgebra.of R (FreeMonoid X)) (FreeMonoid.of x))
    ((MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (FreeMonoid.lift (ι R)))
    (by
      apply MonoidAlgebra.algHom_ext; intro x
      refine FreeMonoid.recOn x ?_ ?_
      · simp
        rfl
      · intro x y ih
        simp at ih
        simp [ih])
    (by
      ext
      simp)
#align free_algebra.equiv_monoid_algebra_free_monoid FreeAlgebra.equivMonoidAlgebraFreeMonoid

def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)
#align free_algebra.algebra_map_inv FreeAlgebra.algebraMapInv

structure map for the algebra.
3. The free algebra `FreeAlgebra R X` is the quotient of `FreeAlgebra.Pre R X` by
  the relation `FreeAlgebra.Rel R X`.
-/


variable (R : Type*) [CommSemiring R]
variable (X : Type*)

namespace FreeAlgebra

/-- This inductive type is used to express representatives of the free algebra.
-/
inductive Pre
  | of : X → Pre
  | ofScalar : R → Pre
  | add : Pre → Pre → Pre
  | mul : Pre → Pre → Pre
#align free_algebra.pre FreeAlgebra.Pre

structure on
the associated quotient.
-/
inductive Rel : Pre R X → Pre R X → Prop
  -- force `ofScalar` to be a central semiring morphism
  | add_scalar {r s : R} : Rel (↑(r + s)) (↑r + ↑s)
  | mul_scalar {r s : R} : Rel (↑(r * s)) (↑r * ↑s)
  | central_scalar {r : R} {a : Pre R X} : Rel (r * a) (a * r)

  -- commutative additive semigroup
  | add_assoc {a b c : Pre R X} : Rel (a + b + c) (a + (b + c))
  | add_comm {a b : Pre R X} : Rel (a + b) (b + a)
  | zero_add {a : Pre R X} : Rel (0 + a) a

  -- multiplicative monoid
  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
  | one_mul {a : Pre R X} : Rel (1 * a) a
  | mul_one {a : Pre R X} : Rel (a * 1) a

  -- distributivity
  | left_distrib {a b c : Pre R X} : Rel (a * (b + c)) (a * b + a * c)
  | right_distrib {a b c : Pre R X} :
      Rel ((a + b) * c) (a * c + b * c)

  -- other relations needed for semiring
  | zero_mul {a : Pre R X} : Rel (0 * a) 0
  | mul_zero {a : Pre R X} : Rel (a * 0) 0

  -- compatibility
  | add_compat_left {a b c : Pre R X} : Rel a b → Rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : Rel a b → Rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : Rel a b → Rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : Rel a b → Rel (c * a) (c * b)
#align free_algebra.rel FreeAlgebra.Rel