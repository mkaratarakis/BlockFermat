def leftMul : G → G → G := fun g : G ↦ fun x : G ↦ g * x
#align left_mul leftMul

def rightMul : G → G → G := fun g : G ↦ fun x : G ↦ x * g
#align right_mul rightMul

def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a
#align npow_rec npowRec

def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a
#align nsmul_rec nsmulRec

def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : ℤ → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹
#align zpow_rec zpowRec

def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : ℕ → G → G := nsmulRec) : ℤ → G → G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a
#align zsmul_rec zsmulRec

def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : ℤ → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = zpow (Int.ofNat n) a  * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl
#align div_inv_monoid DivInvMonoid

def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/-- A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, Sub (Foo X)` instance but no
`∀ X, Neg (Foo X)`. Suppose we also have an instance
`∀ X [Cromulent X], AddGroup (Foo X)`. Then the `(-)` coming from
`AddGroup.sub` cannot be definitionally equal to the `(-)` coming from
`Foo.Sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `AddMonoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl
#align sub_neg_monoid SubNegMonoid

def := div_eq_mul_inv
#align division_def division_def

structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = MetricSpace` and `P = TopologicalSpace`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `MetricSpace` / `TopologicalSpace`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `TopologicalSpace`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `MetricSpace` and
`TopologicalSpace` called `UniformSpace`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`UniformSpace.ofCore` or `RealInnerProduct.ofCore`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/-!
### Design note on `AddMonoid` and `Monoid`

structure `Monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `Algebra.GroupPower.Basic`. For now, we only register the most basic properties that we
need right away.
-/


/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl
#align add_monoid AddMonoid

structure
on a type with the minumum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected mul_left_inv : ∀ a : G, a⁻¹ * a = 1
#align group Group

structure on a type with the minumum proof obligations.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected add_left_neg : ∀ a : A, -a + a = 0
#align add_group AddGroup