def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M →* N →* P) :
    N →* M →* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂
#align monoid_hom.flip MonoidHom.flip

def eval [MulOneClass M] [CommMonoid N] : M →* (M →* N) →* N :=
  (MonoidHom.id (M →* N)).flip
#align monoid_hom.eval MonoidHom.eval

def compHom' [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M →* N) : (N →* P) →* M →* P :=
  flip <| eval.comp f
#align monoid_hom.comp_hom' MonoidHom.compHom'

def compHom [MulOneClass M] [CommMonoid N] [CommMonoid P] :
    (N →* P) →* (M →* N) →* M →* P where
  toFun g := { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f
#align monoid_hom.comp_hom MonoidHom.compHom

def flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} :
    (M →* N →* P) →* N →* M →* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.flip_hom MonoidHom.flipHom

def compl₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q] (f : M →* N →* P)
    (g : Q →* N) : M →* Q →* P :=
  (compHom' g).comp f
#align monoid_hom.compl₂ MonoidHom.compl₂

def compr₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) : M →* N →* Q :=
  (compHom g).comp f
#align monoid_hom.compr₂ MonoidHom.compr₂

def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' a b := AddMonoidHom.ext <| add_mul a b
#align add_monoid_hom.mul AddMonoidHom.mul

def AddMonoid.End.mulLeft : R →+ AddMonoid.End R :=
  AddMonoidHom.mul
#align add_monoid.End.mul_left AddMonoid.End.mulLeft

def AddMonoid.End.mulRight : R →+ AddMonoid.End R :=
  (AddMonoidHom.mul : R →+ AddMonoid.End R).flip
#align add_monoid.End.mul_right AddMonoid.End.mulRight

structure when the target is
commutative, through pointwise multiplication, and with a `CommGroup` structure when the target
is a commutative group. We also prove the same instances for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `Ring` structure on `AddMonoid.End`.
-/


universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

/-- `(M →* N)` is a `CommMonoid` if `N` is commutative. -/
@[to_additive "`(M →+ N)` is an `AddCommMonoid` if `N` is commutative."]
instance MonoidHom.commMonoid [MulOneClass M] [CommMonoid N] :
    CommMonoid (M →* N) where
  mul := (· * ·)
  mul_assoc := by intros; ext; apply mul_assoc
  one := 1
  one_mul := by intros; ext; apply one_mul
  mul_one := by intros; ext; apply mul_one
  mul_comm := by intros; ext; apply mul_comm
  npow n f :=
    { toFun := fun x => f x ^ n, map_one' := by simp, map_mul' := fun x y => by simp [mul_pow] }
  npow_zero f := by
    ext x
    simp
  npow_succ n f := by
    ext x
    simp [pow_succ]

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive "If `G` is an additive commutative group, then `M →+ G` is an additive commutative
      group too."]
instance MonoidHom.commGroup {M G} [MulOneClass M] [CommGroup G] : CommGroup (M →* G) :=
  { MonoidHom.commMonoid with
    inv := Inv.inv,
    div := Div.div,
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv,
    mul_left_inv := by intros; ext; apply mul_left_inv,
    zpow := fun n f =>
      { toFun := fun x => f x ^ n,
        map_one' := by simp,
        map_mul' := fun x y => by simp [mul_zpow] },
    zpow_zero' := fun f => by
      ext x
      simp,
    zpow_succ' := fun n f => by
      ext x
      simp [zpow_natCast, pow_succ],
    zpow_neg' := fun n f => by
      ext x
      simp [Nat.succ_eq_add_one, zpow_natCast, -Int.natCast_add] }

instance AddMonoid.End.instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (AddMonoid.End M) :=
  AddMonoidHom.addCommMonoid

instance AddMonoid.End.instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  { AddMonoid.End.monoid M, AddMonoidHom.addCommMonoid with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl,
    natCast := fun n => n • (1 : AddMonoid.End M),
    natCast_zero := AddMonoid.nsmul_zero _,
    natCast_succ := fun n => AddMonoid.nsmul_succ n 1 }

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
theorem AddMonoid.End.natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) :
    (↑n : AddMonoid.End M) m = n • m :=
  rfl
#align add_monoid.End.nat_cast_apply AddMonoid.End.natCast_apply

structure permits them to be.
-/


section Semiring

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both arguments.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoidHom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgHom.mul`
and `Algebra.lmul`.
-/
def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' a b := AddMonoidHom.ext <| add_mul a b
#align add_monoid_hom.mul AddMonoidHom.mul