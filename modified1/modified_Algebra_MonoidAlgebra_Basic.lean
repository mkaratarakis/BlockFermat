def MonoidAlgebra : Type max u₁ u₂ :=
  G →₀ k
#align monoid_algebra MonoidAlgebra

def liftNC (f : k →+ R) (g : G → R) : MonoidAlgebra k G →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g x)).comp f
#align monoid_algebra.lift_nc MonoidAlgebra.liftNC

def {f g : MonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂) :=
  rfl
#align monoid_algebra.mul_def MonoidAlgebra.mul_def

def : (1 : MonoidAlgebra k G) = single 1 1 :=
  rfl
#align monoid_algebra.one_def MonoidAlgebra.one_def

def (n : ℕ) : (n : MonoidAlgebra k G) = single (1 : G) (n : k) :=
  rfl
#align monoid_algebra.nat_cast_def MonoidAlgebra.nat_cast_def

def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra k G →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }
#align monoid_algebra.lift_nc_ring_hom MonoidAlgebra.liftNCRingHom

def [Ring k] [MulOneClass G] (z : ℤ) :
    (z : MonoidAlgebra k G) = single (1 : G) (z : k) :=
  rfl
#align monoid_algebra.int_cast_def MonoidAlgebra.int_cast_def

def comapDistribMulActionSelf [Group G] [Semiring k] : DistribMulAction G (MonoidAlgebra k G) :=
  Finsupp.comapDistribMulAction
#align monoid_algebra.comap_distrib_mul_action_self MonoidAlgebra.comapDistribMulActionSelf

def ofMagma [Mul G] : G →ₙ* MonoidAlgebra k G where
  toFun a := single a 1
  map_mul' a b := by simp only [mul_def, mul_one, sum_single_index, single_eq_zero, mul_zero]
#align monoid_algebra.of_magma MonoidAlgebra.ofMagma

def of [MulOneClass G] : G →* MonoidAlgebra k G :=
  { ofMagma k G with
    toFun := fun a => single a 1
    map_one' := rfl }
#align monoid_algebra.of MonoidAlgebra.of

def singleHom [MulOneClass G] : k × G →* MonoidAlgebra k G where
  toFun a := single a.2 a.1
  map_one' := rfl
  map_mul' _a _b := single_mul_single.symm
#align monoid_algebra.single_hom MonoidAlgebra.singleHom

def liftMagma [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] :
    (G →ₙ* A) ≃ (MonoidAlgebra k G →ₙₐ[k] A) where
  toFun f :=
    { liftAddHom fun x => (smulAddHom k A).flip (f x) with
      toFun := fun a => a.sum fun m t => t • f m
      map_smul' := fun t' a => by
        -- Porting note(#12129): additional beta reduction needed

def singleOneRingHom [Semiring k] [MulOneClass G] : k →+* MonoidAlgebra k G :=
  { Finsupp.singleAddHom 1 with
    map_one' := rfl
    map_mul' := fun x y => by
      -- Porting note (#10691): Was `rw`.

def mapDomainRingHom (k : Type*) {H F : Type*} [Semiring k] [Monoid G] [Monoid H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F) : MonoidAlgebra k G →+* MonoidAlgebra k H :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }
#align monoid_algebra.map_domain_ring_hom MonoidAlgebra.mapDomainRingHom

def singleOneAlgHom {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    A →ₐ[k] MonoidAlgebra A G :=
  { singleOneRingHom with
    commutes' := fun r => by
      -- Porting note: `ext` → `refine Finsupp.ext fun _ => ?_`
      refine Finsupp.ext fun _ => ?_
      simp
      rfl }
#align monoid_algebra.single_one_alg_hom MonoidAlgebra.singleOneAlgHom

def liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra A G →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }
#align monoid_algebra.lift_nc_alg_hom MonoidAlgebra.liftNCAlgHom

def lift : (G →* A) ≃ (MonoidAlgebra k G →ₐ[k] A) where
  invFun f := (f : MonoidAlgebra k G →* A).comp (of k G)
  toFun F := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
#align monoid_algebra.lift MonoidAlgebra.lift

def (F : G →* A) : ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl
#align monoid_algebra.lift_def MonoidAlgebra.lift_def

def mapDomainNonUnitalAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
    {G H F : Type*} [Mul G] [Mul H] [FunLike F G H] [MulHomClass F G H] (f : F) :
    MonoidAlgebra A G →ₙₐ[k] MonoidAlgebra A H :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra A G →+ MonoidAlgebra A H) with
    map_mul' := fun x y => mapDomain_mul f x y
    map_smul' := fun r x => mapDomain_smul r x }
#align monoid_algebra.map_domain_non_unital_alg_hom MonoidAlgebra.mapDomainNonUnitalAlgHom

def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] (f : F) :
    MonoidAlgebra A G →ₐ[k] MonoidAlgebra A H :=
  { mapDomainRingHom A f with commutes' := mapDomain_algebraMap A f }
#align monoid_algebra.map_domain_alg_hom MonoidAlgebra.mapDomainAlgHom

def domCongr (e : G ≃* H) : MonoidAlgebra A G ≃ₐ[k] MonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (Finsupp.domLCongr e : (G →₀ A) ≃ₗ[k] (H →₀ A))
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul e f g).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongr_toAlgHom (e : G ≃* H) : (domCongr k A e).toAlgHom = mapDomainAlgHom k A e :=
  AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongr_apply (e : G ≃* H) (f : MonoidAlgebra A G) (h : H) :
    domCongr k A e f h = f (e.symm h) :=
  rfl

@[simp] theorem domCongr_support (e : G ≃* H) (f : MonoidAlgebra A G) :
    (domCongr k A e f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single (e : G ≃* H) (g : G) (a : A) :
    domCongr k A e (single g a) = single (e g) a :=
  Finsupp.equivMapDomain_single _ _ _

@[simp] theorem domCongr_refl : domCongr k A (MulEquiv.refl G) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => Finsupp.ext fun _ => rfl

@[simp] theorem domCongr_symm (e : G ≃* H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end lift

section

-- attribute [local reducible] MonoidAlgebra -- Porting note: `reducible` cannot be `local`.

variable (k)

/-- When `V` is a `k[G]`-module, multiplication by a group element `g` is a `k`-linear map. -/
def GroupSMul.linearMap [Monoid G] [CommSemiring k] (V : Type u₃) [AddCommMonoid V] [Module k V]
    [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] (g : G) : V →ₗ[k] V
    where
  toFun v := single g (1 : k) • v
  map_add' x y := smul_add (single g (1 : k)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _
#align monoid_algebra.group_smul.linear_map MonoidAlgebra.GroupSMul.linearMap

def equivariantOfLinearOfComm : V →ₗ[MonoidAlgebra k G] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    -- Porting note(#12129): additional beta reduction needed

def opRingEquiv [Monoid G] :
    (MonoidAlgebra k G)ᵐᵒᵖ ≃+* MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ :=
  { opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv with
    map_mul' := by
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644

def submoduleOfSMulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (MonoidAlgebra k G) V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← Finsupp.sum_single f, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv
#align monoid_algebra.submodule_of_smul_mem MonoidAlgebra.submoduleOfSMulMem

def AddMonoidAlgebra :=
  G →₀ k
#align add_monoid_algebra AddMonoidAlgebra

def liftNC (f : k →+ R) (g : Multiplicative G → R) : k[G] →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g <| Multiplicative.ofAdd x)).comp f
#align add_monoid_algebra.lift_nc AddMonoidAlgebra.liftNC

def {f g : k[G]} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) :=
  rfl
#align add_monoid_algebra.mul_def AddMonoidAlgebra.mul_def

def : (1 : k[G]) = single 0 1 :=
  rfl
#align add_monoid_algebra.one_def AddMonoidAlgebra.one_def

def (n : ℕ) : (n : k[G]) = single (0 : G) (n : k) :=
  rfl
#align add_monoid_algebra.nat_cast_def AddMonoidAlgebra.nat_cast_def

def liftNCRingHom (f : k →+* R) (g : Multiplicative G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    k[G] →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }
#align add_monoid_algebra.lift_nc_ring_hom AddMonoidAlgebra.liftNCRingHom

def [Ring k] [AddZeroClass G] (z : ℤ) :
    (z : k[G]) = single (0 : G) (z : k) :=
  rfl
#align add_monoid_algebra.int_cast_def AddMonoidAlgebra.int_cast_def

def ofMagma [Add G] : Multiplicative G →ₙ* k[G] where
  toFun a := single a 1
  map_mul' a b := by simp only [mul_def, mul_one, sum_single_index, single_eq_zero, mul_zero]; rfl
#align add_monoid_algebra.of_magma AddMonoidAlgebra.ofMagma

def of [AddZeroClass G] : Multiplicative G →* k[G] :=
  { ofMagma k G with
    toFun := fun a => single a 1
    map_one' := rfl }
#align add_monoid_algebra.of AddMonoidAlgebra.of

def of' : G → k[G] := fun a => single a 1
#align add_monoid_algebra.of' AddMonoidAlgebra.of'

def singleHom [AddZeroClass G] : k × Multiplicative G →* k[G] where
  toFun a := single (Multiplicative.toAdd a.2) a.1
  map_one' := rfl
  map_mul' _a _b := single_mul_single.symm
#align add_monoid_algebra.single_hom AddMonoidAlgebra.singleHom

def mapDomainRingHom (k : Type*) [Semiring k] {H F : Type*} [AddMonoid G] [AddMonoid H]
    [FunLike F G H] [AddMonoidHomClass F G H] (f : F) : k[G] →+* k[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }
#align add_monoid_algebra.map_domain_ring_hom AddMonoidAlgebra.mapDomainRingHom

def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) :=
  { Finsupp.domCongr
      Multiplicative.ofAdd with
    toFun := equivMapDomain Multiplicative.ofAdd
    map_mul' := fun x y => by
      -- Porting note: added `dsimp only`; `beta_reduce` alone is not sufficient
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Multiplicative.ofAdd]
      exact MonoidAlgebra.mapDomain_mul (α := Multiplicative G) (β := k)
        (MulHom.id (Multiplicative G)) x y }
#align add_monoid_algebra.to_multiplicative AddMonoidAlgebra.toMultiplicative

def MonoidAlgebra.toAdditive [Semiring k] [Mul G] :
    MonoidAlgebra k G ≃+* AddMonoidAlgebra k (Additive G) :=
  { Finsupp.domCongr Additive.ofMul with
    toFun := equivMapDomain Additive.ofMul
    map_mul' := fun x y => by
      -- Porting note: added `dsimp only`; `beta_reduce` alone is not sufficient
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Additive.ofMul]
      convert MonoidAlgebra.mapDomain_mul (β := k) (MulHom.id G) x y }
#align monoid_algebra.to_additive MonoidAlgebra.toAdditive

def liftMagma [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] :
    (Multiplicative G →ₙ* A) ≃ (k[G] →ₙₐ[k] A) :=
  { (MonoidAlgebra.liftMagma k : (Multiplicative G →ₙ* A) ≃ (_ →ₙₐ[k] A)) with
    toFun := fun f =>
      { (MonoidAlgebra.liftMagma k f : _) with
        toFun := fun a => sum a fun m t => t • f (Multiplicative.ofAdd m) }
    invFun := fun F => F.toMulHom.comp (ofMagma k G) }
#align add_monoid_algebra.lift_magma AddMonoidAlgebra.liftMagma

def singleZeroRingHom [Semiring k] [AddMonoid G] : k →+* k[G] :=
  { Finsupp.singleAddHom 0 with
    map_one' := rfl
    -- Porting note (#10691): Was `rw`.

def opRingEquiv [AddCommMonoid G] :
    k[G]ᵐᵒᵖ ≃+* kᵐᵒᵖ[G] :=
  { MulOpposite.opAddEquiv.symm.trans
      (Finsupp.mapRange.addEquiv (MulOpposite.opAddEquiv : k ≃+ kᵐᵒᵖ)) with
    map_mul' := by
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644

def singleZeroAlgHom [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] : k →ₐ[R] k[G] :=
  { singleZeroRingHom with
    commutes' := fun r => by
      -- Porting note: `ext` → `refine Finsupp.ext fun _ => ?_`
      refine Finsupp.ext fun _ => ?_
      simp
      rfl }
#align add_monoid_algebra.single_zero_alg_hom AddMonoidAlgebra.singleZeroAlgHom

def liftNCAlgHom (f : A →ₐ[k] B) (g : Multiplicative G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[G] →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }
#align add_monoid_algebra.lift_nc_alg_hom AddMonoidAlgebra.liftNCAlgHom

def lift : (Multiplicative G →* A) ≃ (k[G] →ₐ[k] A) :=
  { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ with
    invFun := fun f => (f : k[G] →* A).comp (of k G)
    toFun := fun F =>
      { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ F with
        toFun := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _ } }
#align add_monoid_algebra.lift AddMonoidAlgebra.lift

def (F : Multiplicative G →* A) :
    ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl
#align add_monoid_algebra.lift_def AddMonoidAlgebra.lift_def

def mapDomainNonUnitalAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
    {G H F : Type*} [Add G] [Add H] [FunLike F G H] [AddHomClass F G H] (f : F) :
    A[G] →ₙₐ[k] A[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra A G →+ MonoidAlgebra A H) with
    map_mul' := fun x y => mapDomain_mul f x y
    map_smul' := fun r x => mapDomain_smul r x }
#align add_monoid_algebra.map_domain_non_unital_alg_hom AddMonoidAlgebra.mapDomainNonUnitalAlgHom

def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [AddMonoid G]
    {H F : Type*} [AddMonoid H] [FunLike F G H] [AddMonoidHomClass F G H] (f : F) :
    A[G] →ₐ[k] A[H] :=
  { mapDomainRingHom A f with commutes' := mapDomain_algebraMap A f }
#align add_monoid_algebra.map_domain_alg_hom AddMonoidAlgebra.mapDomainAlgHom

def domCongr (e : G ≃+ H) : A[G] ≃ₐ[k] A[H] :=
  AlgEquiv.ofLinearEquiv
    (Finsupp.domLCongr e : (G →₀ A) ≃ₗ[k] (H →₀ A))
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul e f g).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongr_toAlgHom (e : G ≃+ H) : (domCongr k A e).toAlgHom = mapDomainAlgHom k A e :=
  AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongr_apply (e : G ≃+ H) (f : MonoidAlgebra A G) (h : H) :
    domCongr k A e f h = f (e.symm h) :=
  rfl

@[simp] theorem domCongr_support (e : G ≃+ H) (f : MonoidAlgebra A G) :
    (domCongr k A e f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single (e : G ≃+ H) (g : G) (a : A) :
    domCongr k A e (single g a) = single (e g) a :=
  Finsupp.equivMapDomain_single _ _ _

@[simp] theorem domCongr_refl : domCongr k A (AddEquiv.refl G) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => Finsupp.ext fun _ => rfl

@[simp] theorem domCongr_symm (e : G ≃+ H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end AddMonoidAlgebra

variable [CommSemiring R]

/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
def AddMonoidAlgebra.toMultiplicativeAlgEquiv [Semiring k] [Algebra R k] [AddMonoid G] :
    AddMonoidAlgebra k G ≃ₐ[R] MonoidAlgebra k (Multiplicative G) :=
  { AddMonoidAlgebra.toMultiplicative k G with
    commutes' := fun r => by simp [AddMonoidAlgebra.toMultiplicative] }
#align add_monoid_algebra.to_multiplicative_alg_equiv AddMonoidAlgebra.toMultiplicativeAlgEquiv

def MonoidAlgebra.toAdditiveAlgEquiv [Semiring k] [Algebra R k] [Monoid G] :
    MonoidAlgebra k G ≃ₐ[R] AddMonoidAlgebra k (Additive G) :=
  { MonoidAlgebra.toAdditive k G with commutes' := fun r => by simp [MonoidAlgebra.toAdditive] }
#align monoid_algebra.to_additive_alg_equiv MonoidAlgebra.toAdditiveAlgEquiv

structure is known as the "monoid algebra",
i.e. the finite formal linear combinations over a given semiring of elements of the monoid.
The "group ring" ℤ[G] or the "group algebra" k[G] are typical uses.

In fact the construction of the "monoid algebra" makes sense when `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all. In this case the construction yields a not-necessarily-unital,
not-necessarily-associative algebra but it is still adjoint to the forgetful functor from such
algebras to magmas, and we prove this as `MonoidAlgebra.liftMagma`.

In this file we define `MonoidAlgebra k G := G →₀ k`, and `AddMonoidAlgebra k G`
in the same way, and then define the convolution product on these.

When the domain is additive, this is used to define polynomials:
```
Polynomial R := AddMonoidAlgebra R ℕ
MvPolynomial σ α := AddMonoidAlgebra R (σ →₀ ℕ)
```

When the domain is multiplicative, e.g. a group, this will be used to define the group ring.

## Notation

structure -/


section Semiring

variable [Semiring k] [Monoid G]

instance semiring : Semiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalSemiring,
    MonoidAlgebra.nonAssocSemiring with }
#align monoid_algebra.semiring MonoidAlgebra.semiring

structure -/


section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Mul G]

instance isScalarTower_self [IsScalarTower R k k] :
    IsScalarTower R (MonoidAlgebra k G) (MonoidAlgebra k G) :=
  ⟨fun t a b => by
    -- Porting note: `ext` → `refine Finsupp.ext fun _ => ?_`
    refine Finsupp.ext fun m => ?_
    -- Porting note: `refine` & `rw` are required because `simp` behaves differently.
    classical
      simp only [smul_eq_mul, mul_apply]
      rw [coe_smul]
      refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
        simp only [mul_apply, Finsupp.smul_sum, smul_ite, smul_mul_assoc,
          zero_mul, ite_self, imp_true_iff, sum_zero, Pi.smul_apply, smul_zero]⟩
#align monoid_algebra.is_scalar_tower_self MonoidAlgebra.isScalarTower_self

structure -/


section Algebra

-- attribute [local reducible] MonoidAlgebra -- Porting note: `reducible` cannot be `local`.

theorem single_one_comm [CommSemiring k] [MulOneClass G] (r : k) (f : MonoidAlgebra k G) :
    single (1 : G) r * f = f * single (1 : G) r :=
  single_commute Commute.one_left (Commute.all _) f
#align monoid_algebra.single_one_comm MonoidAlgebra.single_one_comm

structure -/


section Semiring

instance smulZeroClass [Semiring k] [SMulZeroClass R k] : SMulZeroClass R k[G] :=
  Finsupp.smulZeroClass
#align add_monoid_algebra.smul_zero_class AddMonoidAlgebra.smulZeroClass

structure -/


section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Add G]

instance isScalarTower_self [IsScalarTower R k k] :
    IsScalarTower R k[G] k[G] :=
  @MonoidAlgebra.isScalarTower_self k (Multiplicative G) R _ _ _ _
#align add_monoid_algebra.is_scalar_tower_self AddMonoidAlgebra.isScalarTower_self

structure -/


section Algebra

-- attribute [local reducible] MonoidAlgebra -- Porting note: `reducible` cannot be `local`.

/-- `Finsupp.single 0` as a `RingHom` -/
@[simps]
def singleZeroRingHom [Semiring k] [AddMonoid G] : k →+* k[G] :=
  { Finsupp.singleAddHom 0 with
    map_one' := rfl
    -- Porting note (#10691): Was `rw`.