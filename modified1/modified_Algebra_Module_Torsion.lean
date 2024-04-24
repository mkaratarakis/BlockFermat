def torsionOf (x : M) : Ideal R :=
  -- Porting note (#11036): broken dot notation on LinearMap.ker Lean4#1910

def quotTorsionOfEquivSpanSingleton (x : M) : (R ⧸ torsionOf R M x) ≃ₗ[R] R ∙ x :=
  (LinearMap.toSpanSingleton R M x).quotKerEquivRange.trans <|
    LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R M x).symm
#align ideal.quot_torsion_of_equiv_span_singleton Ideal.quotTorsionOfEquivSpanSingleton

def torsionBy (a : R) : Submodule R M :=
  -- Porting note (#11036): broken dot notation on LinearMap.ker Lean4#1910

def torsionBySet (s : Set R) : Submodule R M :=
  sInf (torsionBy R M '' s)
#align submodule.torsion_by_set Submodule.torsionBySet

def torsion'AddSubMonoid (S : Type*) [CommMonoid S] [DistribMulAction S M] :
    AddSubmonoid M where
  carrier := { x | ∃ a : S, a • x = 0 }
  add_mem' := by
    intro x y ⟨a,hx⟩ ⟨b,hy⟩
    use b * a
    rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zero]
  zero_mem' := ⟨1, smul_zero 1⟩

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps!]
def torsion' (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M] :
    Submodule R M :=
  { torsion'AddSubMonoid M S with
    smul_mem' := fun a x ⟨b, h⟩ => ⟨b, by rw [smul_comm, h, smul_zero]⟩}
#align submodule.torsion' Submodule.torsion'

def torsion :=
  torsion' R M R⁰
#align submodule.torsion Submodule.torsion

def IsTorsionBy (a : R) :=
  ∀ ⦃x : M⦄, a • x = 0
#align module.is_torsion_by Module.IsTorsionBy

def IsTorsionBySet (s : Set R) :=
  ∀ ⦃x : M⦄ ⦃a : s⦄, (a : R) • x = 0
#align module.is_torsion_by_set Module.IsTorsionBySet

def IsTorsion' (S : Type*) [SMul S M] :=
  ∀ ⦃x : M⦄, ∃ a : S, a • x = 0
#align module.is_torsion' Module.IsTorsion'

def IsTorsion :=
  ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0
#align module.is_torsion Module.IsTorsion

def IsTorsionBySet.hasSMul : SMul (R ⧸ I) M where
  smul b x :=
    Quotient.liftOn' b (· • x) fun b₁ b₂ h =>
      show b₁ • x = b₂ • x from by
        have : (-b₁ + b₂) • x = 0 := @hM x ⟨_, QuotientAddGroup.leftRel_apply.mp h⟩
        rw [add_smul, neg_smul, neg_add_eq_zero] at this
        exact this
#align module.is_torsion_by_set.has_smul Module.IsTorsionBySet.hasSMul

def IsTorsionBySet.module : Module (R ⧸ I) M :=
  @Function.Surjective.moduleLeft _ _ _ _ _ _ _ hM.hasSMul _ Ideal.Quotient.mk_surjective
    (IsTorsionBySet.mk_smul hM)
#align module.is_torsion_by_set.module Module.IsTorsionBySet.module

def quotientAnnihilator : Module (R ⧸ Module.annihilator R M) M :=
  (isTorsionBySet_annihilator R M).module

instance : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  IsTorsionBySet.module (R := R) (I := I) fun x r => by
    induction x using Quotient.inductionOn
    refine' (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul r.prop _)
    trivial

end Module

namespace Submodule

instance (I : Ideal R) : Module (R ⧸ I) (torsionBySet R M I) :=
  -- Porting note: times out without the (R := R)
  Module.IsTorsionBySet.module <| torsionBySet_isTorsionBySet (R := R) I

@[simp]
theorem torsionBySet.mk_smul (I : Ideal R) (b : R) (x : torsionBySet R M I) :
    Ideal.Quotient.mk I b • x = b • x :=
  rfl
#align submodule.torsion_by_set.mk_smul Submodule.torsionBySet.mk_smul

def submodule_torsionBy_orderIso (a : R) :
    Submodule (R ⧸ R ∙ a) (torsionBy R M a) ≃o Submodule R (torsionBy R M a) :=
  { restrictScalarsEmbedding R (R ⧸ R ∙ a) (torsionBy R M a) with
    invFun := fun p ↦
      { carrier := p
        add_mem' := add_mem
        zero_mem' := p.zero_mem
        smul_mem' := by rintro ⟨b⟩; exact p.smul_mem b }
    left_inv := by intro; ext; simp [restrictScalarsEmbedding]
    right_inv := by intro; ext; simp [restrictScalarsEmbedding] }

end Submodule

end NeedsGroup

namespace Submodule

section Torsion'

open Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

@[simp]
theorem mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 :=
  Iff.rfl
#align submodule.mem_torsion'_iff Submodule.mem_torsion'_iff

def pOrder {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M)
    [∀ n : ℕ, Decidable (p ^ n • x = 0)] :=
  Nat.find <| (isTorsion'_powers_iff p).mp hM x
#align submodule.p_order Submodule.pOrder