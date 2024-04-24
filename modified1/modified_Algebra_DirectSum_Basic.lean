def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ :=
  -- Porting note: Failed to synthesize
  -- Π₀ i, β i deriving AddCommMonoid, Inhabited
  -- See https://github.com/leanprover-community/mathlib4/issues/5020
  Π₀ i, β i
#align direct_sum DirectSum

def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i
    where
  toFun := DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero
#align direct_sum.mk DirectSum.mk

def of (i : ι) : β i →+ ⨁ i, β i :=
  DFinsupp.singleAddHom β i
#align direct_sum.of DirectSum.of

def toAddMonoid : (⨁ i, β i) →+ γ :=
  DFinsupp.liftAddHom (β := β) φ
#align direct_sum.to_add_monoid DirectSum.toAddMonoid

def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)
#align direct_sum.from_add_monoid DirectSum.fromAddMonoid

def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  toAddMonoid fun i => of (fun i : Subtype T => β i) ⟨↑i, H i.2⟩
#align direct_sum.set_to_set DirectSum.setToSet

def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  {
    DirectSum.toAddMonoid fun _ =>
      AddMonoidHom.id
        M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv := fun x =>
      DirectSum.induction_on x (by rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of]; rfl) fun x y ihx ihy => by
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy]
    right_inv := fun x => toAddMonoid_of _ _ _ }
#align direct_sum.id DirectSum.id

def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv}
#align direct_sum.equiv_congr_left DirectSum.equivCongrLeft

def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }
#align direct_sum.add_equiv_prod_direct_sum DirectSum.addEquivProdDirectSum

def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j
    where
  toFun := DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g
#align direct_sum.sigma_curry DirectSum.sigmaCurry

def sigmaUncurry [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ (i) (j), δ i j) →+ ⨁ i : Σ _i, _, δ i.1 i.2
    where
  toFun := DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add
#align direct_sum.sigma_uncurry DirectSum.sigmaUncurry

def sigmaCurryEquiv [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry, DFinsupp.sigmaCurryEquiv with }
#align direct_sum.sigma_curry_equiv DirectSum.sigmaCurryEquiv

def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)
#align direct_sum.coe_add_monoid_hom DirectSum.coeAddMonoidHom

def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)
#align direct_sum.is_internal DirectSum.IsInternal