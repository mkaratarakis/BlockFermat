def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulActionSemiHomClass F φ X Y`
  into an actual `MulActionHom`.
  This is declared as the default coercion from `F` to `MulActionSemiHom φ X Y`. -/
@[coe]
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X →ₑ[φ] Y where
  toFun := DFunLike.coe f
  map_smul' := map_smulₛₗ f

/-- Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`. -/
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X →ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩

variable (M' X Y F) in
/-- If Y/X/M forms a scalar tower, any map X → Y preserving X-action also preserves M-action. -/
theorem _root_.IsScalarTower.smulHomClass [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
    [MulActionHomClass F X X Y] : MulActionHomClass F M' X Y where
  map_smulₛₗ f m x := by
    rw [← mul_one (m • x), ← smul_eq_mul, map_smul, smul_assoc, ← map_smul,
      smul_eq_mul, mul_one, id_eq]

protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul f m x
#align mul_action_hom.map_smul MulActionHom.map_smul

def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y
    where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a
#align equivariant_map.of_eq MulActionHom.ofEq

def id : X →[M] X :=
  ⟨id, fun _ _ => rfl⟩
#align mul_action_hom.id MulActionHom.id

def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
    X →ₑ[χ] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩
#align mul_action_hom.comp MulActionHom.comp

def inverse (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ →[M] X
    where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul, id_eq]
      _ = m • g x := by rw [h₁]


/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse' (f : X →ₑ[φ] Y) (g : Y → X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    Y →ₑ[φ'] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]
#align mul_action_hom.inverse MulActionHom.inverse'

def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom

end MulActionHom

section DistribMulAction

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable {P : Type*} [Monoid P]
variable (φ: M →* N) (φ' : N →* M) (ψ : N →* P) (χ : M →* P)
variable (A : Type*) [AddMonoid A] [DistribMulAction M A]
variable (B : Type*) [AddMonoid B] [DistribMulAction N B]
variable (B₁ : Type*) [AddMonoid B₁] [DistribMulAction M B₁]
variable (C : Type*) [AddMonoid C] [DistribMulAction P C]

variable (A' : Type*) [AddGroup A'] [DistribMulAction M A']
variable (B' : Type*) [AddGroup B'] [DistribMulAction N B']

/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →ₑ[φ] B, A →+ B
#align distrib_mul_action_hom DistribMulActionHom

def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulActionHomClass F M X Y` into an actual
`MulActionHom`. This is declared as the default coercion from `F` to `MulActionHom M X Y`. -/
@[coe]
def _root_.DistribMulActionSemiHomClass.toDistribMulActionHom
    [DistribMulActionSemiHomClass F φ A B]
    (f : F) : A →ₑ+[φ] B :=
  { (f : A →+ B),  (f : A →ₑ[φ] B) with }

/-- Any type satisfying `MulActionHomClass` can be cast into `MulActionHom`
via `MulActionHomClass.toMulActionHom`. -/
instance [DistribMulActionSemiHomClass F φ A B] :
  CoeTC F (A →ₑ+[φ] B) :=
  ⟨DistribMulActionSemiHomClass.toDistribMulActionHom⟩

/-- If `DistribMulAction` of `M` and `N` on `A` commute,
  then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism. -/
@[simps]
def _root_.SMulCommClass.toDistribMulActionHom {M} (N A : Type*) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[simp]
theorem toFun_eq_coe (f : A →ₑ+[φ] B) : f.toFun = f := rfl
#align distrib_mul_action_hom.to_fun_eq_coe DistribMulActionHom.toFun_eq_coe

def id : A →+[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩
#align distrib_mul_action_hom.id DistribMulActionHom.id

def comp (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₑ+[χ] C :=
  { MulActionHom.comp (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B),
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }
#align distrib_mul_action_hom.comp DistribMulActionHom.comp

def inverse (f : A →+[M] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →+[M] A :=
  { (f : A →+ B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }
#align distrib_mul_action_hom.inverse DistribMulActionHom.inverse

def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` into an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`. -/
@[coe]
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S]
    (f : F) : R →ₑ+*[φ] S :=
 { (f : R →+* S),  (f : R →ₑ+[φ] S) with }

/-- Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringActionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`. -/
instance [MulSemiringActionSemiHomClass F φ R S] :
    CoeTC F (R →ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
theorem coe_fn_coe (f : R →ₑ+*[φ] S) : ⇑(f : R →+* S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe MulSemiringActionHom.coe_fn_coe

def id : R →+*[M] R :=
  ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩
#align mul_semiring_action_hom.id MulSemiringActionHom.id

def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R →ₑ+*[χ] T :=
  { DistribMulActionHom.comp (g : S →ₑ+[ψ] T) (f : R →ₑ+[φ] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }

@[simp]
theorem comp_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
    g.comp f x = g (f x) := rfl

@[simp]
theorem id_comp (f : R →ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : R →ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_semiring_action_hom.comp_id MulSemiringActionHom.comp_id

def inverse' (f : R →ₑ+*[φ] S) (g : S → R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S →ₑ+*[φ'] R :=
  { (f : R →+ S).inverse g h₁ h₂,
    (f : R →* S).inverse g h₁ h₂,
    (f : R →ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R →+*[M] S₁) (g : S₁ → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S₁ →+*[M] R :=
  { (f : R →+ S₁).inverse g h₁ h₂,
    (f : R →* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }
#align mul_semiring_action_hom.inverse MulSemiringActionHom.inverse

structure and `φ`-equivariant
* `SMulSemiringHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

## Notation

structure MulActionHom where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
 see https://github.com/leanprover/lean4/issues/2000 -/
/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act on `X` and `Y` respectively -/
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the action of `M`

This is the same as `X →ₑ[@id M] Y` -/
notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y



/-- `MulActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionHom`. -/
class MulActionSemiHomClass (F : Type*)
    {M N : outParam (Type*)} (φ : outParam (M → N))
    (X Y : outParam (Type*)) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop
   where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)
#align smul_hom_class MulActionSemiHomClass

structure DistribMulActionHom extends A →ₑ[φ] B, A →+ B
#align distrib_mul_action_hom DistribMulActionHom

structure and equivariant with respect to `φ`.
    You should extend this class when you extend `DistribMulActionSemiHom`. -/
class DistribMulActionSemiHomClass (F : Type*)
    {M N : outParam (Type*)} (φ : outParam (M → N))
    (A B : outParam (Type*))
    [Monoid M] [Monoid N]
    [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
    [FunLike F A B]
    extends MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B : Prop
#align distrib_mul_action_hom_class DistribMulActionSemiHomClass

structure and equivariant with respect to the action of `M`.
    It is an abbreviation to `DistribMulActionHomClass F (MonoidHom.id M) A B`
You should extend this class when you extend `DistribMulActionHom`. -/
abbrev DistribMulActionHomClass (F : Type*) (M : outParam (Type*))
    (A B : outParam (Type*)) [Monoid M] [AddMonoid A] [AddMonoid B]
    [DistribMulAction M A] [DistribMulAction M B] [FunLike F A B] :=
    DistribMulActionSemiHomClass F (MonoidHom.id M) A B

/- porting note: Removed a @[nolint dangerousInstance] for
DistribMulActionHomClass.toAddMonoidHomClass not dangerous due to `outParam`s -/

namespace DistribMulActionHom

/- Porting note (#11215): TODO decide whether the next two instances should be removed

structure MulSemiringActionHom extends R →ₑ+[φ] S, R →+* S
#align mul_semiring_action_hom MulSemiringActionHom

structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`. -/
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam (Type*)} [Monoid M] [Monoid N]
    (φ : outParam (M → N))
    (R S : outParam (Type*)) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S]
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S : Prop
#align mul_semiring_action_hom_class MulSemiringActionSemiHomClass

structure and equivariant with respect to a `DistribMulAction`of `M` on `R` and `S` .
 -/
abbrev MulSemiringActionHomClass
    (F : Type*)
    {M : outParam (Type*)} [Monoid M]
    (R S : outParam (Type*)) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] [FunLike F R S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

/- porting note: Removed a @[nolint dangerousInstance] for MulSemiringActionHomClass.toRingHomClass
 not dangerous due to outParam -/

namespace MulSemiringActionHom

/- Porting note (#11215): TODO decide whether the next two instances should be removed