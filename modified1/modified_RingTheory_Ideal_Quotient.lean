def ringCon (I : Ideal R) : RingCon R :=
  { QuotientAddGroup.con I.toAddSubgroup with
    mul' := fun {a₁ b₁ a₂ b₂} h₁ h₂ => by
      rw [Submodule.quotientRel_r_def] at h₁ h₂ ⊢
      have F := I.add_mem (I.mul_mem_left a₂ h₁) (I.mul_mem_right b₁ h₂)
      have : a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ := by
        rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁]
      rwa [← this] at F }
#align ideal.quotient.ring_con Ideal.Quotient.ringCon

def mk (I : Ideal R) : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
#align ideal.quotient.mk Ideal.Quotient.mk

def groupWithZero (I : Ideal R) [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) :=
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a ≠ 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl }
#align ideal.quotient.group_with_zero Ideal.Quotient.groupWithZero

def field (I : Ideal R) [hI : I.IsMaximal] : Field (R ⧸ I) :=
  { Quotient.commRing I, Quotient.groupWithZero I with qsmul := qsmulRec _ }
#align ideal.quotient.field Ideal.Quotient.field

def lift (I : Ideal R) (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }
#align ideal.quotient.lift Ideal.Quotient.lift

def factor (S T : Ideal R) (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)
#align ideal.quotient.factor Ideal.Quotient.factor

def quotEquivOfEq {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }
#align ideal.quot_equiv_of_eq Ideal.quotEquivOfEq

def piQuotEquiv : ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] ι → (R ⧸ I) where
  toFun := fun x ↦
      Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun a b hab =>
        funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun := fun x ↦ Ideal.Quotient.mk (I.pi ι) fun i ↦ Quotient.out' (x i)
  left_inv := by
    rintro ⟨x⟩
    exact Ideal.Quotient.eq.2 fun i => Ideal.Quotient.eq.1 (Quotient.out_eq' _)
  right_inv := by
    intro x
    ext i
    obtain ⟨_, _⟩ := @Quot.exists_rep _ _ (x i)
    convert Quotient.out_eq' (x i)
#align ideal.pi_quot_equiv Ideal.piQuotEquiv