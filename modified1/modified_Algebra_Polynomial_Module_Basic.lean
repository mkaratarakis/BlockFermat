def AEval (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : A) := M

instance AEval.instAddCommGroup {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    AddCommGroup <| AEval R M a := inferInstanceAs (AddCommGroup M)

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

namespace AEval

instance instAddCommMonoid : AddCommMonoid <| AEval R M a := inferInstanceAs (AddCommMonoid M)

instance instModuleOrig : Module R <| AEval R M a := inferInstanceAs (Module R M)

instance instFiniteOrig [Finite R M] : Finite R <| AEval R M a := inferInstanceAs (Finite R M)

instance instModulePolynomial : Module R[X] <| AEval R M a := compHom M (aeval a).toRingHom

variable (R M)
/--
The canonical linear equivalence between `M` and `Module.AEval R M a` as an `R`-module.
-/
def of : M ≃ₗ[R] AEval R M a :=
  LinearEquiv.refl _ _

variable {R M}

lemma of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a m := rfl

@[simp] lemma of_symm_smul (f : R[X]) (m : AEval R M a) :
    (of R M a).symm (f • m) = aeval a f • (of R M a).symm m := rfl

@[simp] lemma C_smul (t : R) (m : AEval R M a) : C t • m = t • m :=
  (of R M a).symm.injective <| by simp

lemma X_smul_of (m : M) : (X : R[X]) • (of R M a m) = of R M a (a • m) := by
  rw [← of_aeval_smul, aeval_X]

lemma of_symm_X_smul (m : AEval R M a) :
    (of R M a).symm ((X : R[X]) • m) = a • (of R M a).symm m := by
  rw [of_symm_smul, aeval_X]

instance instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] <| AEval R M a where
  smul_assoc r f m := by
    apply (of R M a).symm.injective
    rw [of_symm_smul, map_smul, smul_assoc, map_smul, of_symm_smul]

instance instFinitePolynomial [Finite R M] : Finite R[X] <| AEval R M a :=
  Finite.of_restrictScalars_finite R _ _

/-- Construct an `R[X]`-linear map out of `AEval R M a` from a `R`-linear map out of `M`. -/
def _root_.LinearMap.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M →ₗ[R] N) (hf : ∀ m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a →ₗ[R[X]] N where
  __ := f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m ↦ by simp [C_eq_algebraMap])
    (fun p q hp hq m ↦ by simp_all [add_smul]) fun n k h m ↦ by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h ⊢
      simp_rw [pow_succ, ← mul_assoc, mul_smul _ X, ← hf, ← of_symm_X_smul, ← h]

lemma annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator R[X] (AEval R M a) = RingHom.ker (aeval a) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

@[simp]
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule R[X] <| AEval R M a).annihilator = RingHom.ker (aeval a) := by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

section Submodule

variable {p : Submodule R M} (hp : p ≤ p.comap (Algebra.lsmul R R M a))
  {q : Submodule R[X] <| AEval R M a}

variable (R M) in
/-- We can turn an `R[X]`-submodule into an `R`-submodule by forgetting the action of `X`. -/
def comapSubmodule :
    CompleteLatticeHom (Submodule R[X] <| AEval R M a) (Submodule R M) :=
  (Submodule.orderIsoMapComap (of R M a)).symm.toCompleteLatticeHom.comp <|
    Submodule.restrictScalarsLatticeHom R R[X] (AEval R M a)

@[simp] lemma mem_comapSubmodule {x : M} :
    x ∈ comapSubmodule R M a q ↔ of R M a x ∈ q :=
  Iff.rfl

@[simp] lemma comapSubmodule_le_comap :
    comapSubmodule R M a q ≤ (comapSubmodule R M a q).comap (Algebra.lsmul R R M a) := by
  intro m hm
  simpa only [Submodule.mem_comap, Algebra.lsmul_coe, mem_comapSubmodule, ← X_smul_of] using
    q.smul_mem (X : R[X]) hm

/-- An `R`-submodule which is stable under the action of `a` can be promoted to an
`R[X]`-submodule. -/
def mapSubmodule : Submodule R[X] <| AEval R M a :=
  { toAddSubmonoid := p.toAddSubmonoid.map (of R M a)
    smul_mem' := by
      rintro f - ⟨m : M, h : m ∈ p, rfl⟩
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, AddSubmonoid.mem_map,
        Submodule.mem_toAddSubmonoid]
      exact ⟨aeval a f • m, aeval_apply_smul_mem_of_le_comap' h f a hp, of_aeval_smul a f m⟩ }

@[simp] lemma mem_mapSubmodule {m : AEval R M a} :
    m ∈ mapSubmodule a hp ↔ (of R M a).symm m ∈ p :=
  ⟨fun ⟨_, hm, hm'⟩ ↦ hm'.symm ▸ hm, fun hm ↦ ⟨(of R M a).symm m, hm, rfl⟩⟩

@[simp] lemma mapSubmodule_comapSubmodule (h := comapSubmodule_le_comap a) :
    mapSubmodule a (p := comapSubmodule R M a q) h = q := by
  ext; simp

@[simp] lemma comapSubmodule_mapSubmodule :
    comapSubmodule R M a (mapSubmodule a hp) = p := by
  ext; simp

variable (R M)

lemma injective_comapSubmodule : Injective (comapSubmodule R M a) := by
  intro q₁ q₂ hq
  rw [← mapSubmodule_comapSubmodule (q := q₁), ← mapSubmodule_comapSubmodule (q := q₂)]
  simp_rw [hq]

lemma range_comapSubmodule :
    range (comapSubmodule R M a) = {p | p ≤ p.comap (Algebra.lsmul R R M a)} :=
  le_antisymm (fun _ ⟨_, hq⟩ ↦ hq ▸ comapSubmodule_le_comap a)
    (fun _ hp ↦ ⟨mapSubmodule a hp, comapSubmodule_mapSubmodule a hp⟩)

end Submodule

end AEval

variable (φ : M →ₗ[R] M)
/--
Given and `R`-module `M` and a linear map `φ : M →ₗ[R] M`, `Module.AEval' φ` is loosely speaking
the `R[X]`-module with elements `m : M`, where the action of a polynomial $f$ is given by
$f • m = f(a) • m$.

More precisely, `Module.AEval' φ` has elements `Module.AEval'.of φ m` for `m : M`,
and the action of `f` is `f • (of φ m) = of φ ((aeval φ f) • m)`.

`Module.AEval'` is defined as a special case of `Module.AEval` in which the `R`-algebra is
`M →ₗ[R] M`. Lemmas involving `Module.AEval` may be applied to `Module.AEval'`.
-/
abbrev AEval' := AEval R M φ
/--
The canonical linear equivalence between `M` and `Module.AEval' φ` as an `R`-module,
where `φ : M →ₗ[R] M`.
-/
abbrev AEval'.of : M ≃ₗ[R] AEval' φ := AEval.of R M φ
lemma AEval'_def : AEval' φ = AEval R M φ := rfl
lemma AEval'.X_smul_of (m : M) : (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m) :=
  AEval.X_smul_of _ _
lemma AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((X : R[X]) • m) = φ ((AEval'.of φ).symm m) := AEval.of_symm_X_smul _ _

instance [Finite R M] : Finite R[X] <| AEval' φ := inferInstance

end Module

/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules

def PolynomialModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] := ℕ →₀ M
#align polynomial_module PolynomialModule

def single (i : ℕ) : M →+ PolynomialModule R M :=
  Finsupp.singleAddHom i
#align polynomial_module.single PolynomialModule.single

def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  Finsupp.lsingle i
#align polynomial_module.lsingle PolynomialModule.lsingle

def (f : R[X]) (m : PolynomialModule R M) :
    f • m = aeval (Finsupp.lmapDomain M R Nat.succ) f m := by
  rfl

instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) :=
  Finsupp.isScalarTower _ _

instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) := by
  haveI : IsScalarTower R R[X] (PolynomialModule R M) :=
    inferInstanceAs <| IsScalarTower R R[X] <| Module.AEval' <| Finsupp.lmapDomain M R Nat.succ
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]
#align polynomial_module.is_scalar_tower' PolynomialModule.isScalarTower'

def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] :=
  { (Polynomial.toFinsuppIso R).symm with
    map_smul' := fun r x => by
      dsimp
      rw [← RingEquiv.coe_toEquiv_symm, RingEquiv.coe_toEquiv]
      induction' x using induction_linear with _ _ hp hq n a
      · rw [smul_zero, map_zero, mul_zero]
      · rw [smul_add, map_add, map_add, mul_add, hp, hq]
      · ext i
        simp only [coeff_ofFinsupp, smul_single_apply, toFinsuppIso_symm_apply, coeff_ofFinsupp,
        single_apply, ge_iff_le, smul_eq_mul, Polynomial.coeff_mul, mul_ite, mul_zero]
        split_ifs with hn
        · rw [Finset.sum_eq_single (i - n, n)]
          simp only [ite_true]
          · rintro ⟨p, q⟩ hpq1 hpq2
            rw [Finset.mem_antidiagonal] at hpq1
            split_ifs with H
            · dsimp at H
              exfalso
              apply hpq2
              rw [← hpq1, H]
              simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
            · rfl
          · intro H
            exfalso
            apply H
            rw [Finset.mem_antidiagonal, tsub_add_cancel_of_le hn]
        · symm
          rw [Finset.sum_ite_of_false, Finset.sum_const_zero]
          simp_rw [Finset.mem_antidiagonal]
          intro x hx
          contrapose! hn
          rw [add_comm, ← hn] at hx
          exact Nat.le.intro hx }
#align polynomial_module.equiv_polynomial_self PolynomialModule.equivPolynomialSelf

def equivPolynomial {S : Type*} [CommRing S] [Algebra R S] :
    PolynomialModule R S ≃ₗ[R] S[X] :=
  { (Polynomial.toFinsuppIso S).symm with map_smul' := fun _ _ => rfl }
#align polynomial_module.equiv_polynomial PolynomialModule.equivPolynomial

def map (f : M →ₗ[R] M') : PolynomialModule R M →ₗ[R] PolynomialModule R' M' :=
  Finsupp.mapRange.linearMap f
#align polynomial_module.map PolynomialModule.map

def eval (r : R) : PolynomialModule R M →ₗ[R] M where
  toFun p := p.sum fun i m => r ^ i • m
  map_add' x y := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine' (Finsupp.sum_smul_index' _).trans _
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]
#align polynomial_module.eval PolynomialModule.eval

def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
  LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))
#align polynomial_module.comp PolynomialModule.comp