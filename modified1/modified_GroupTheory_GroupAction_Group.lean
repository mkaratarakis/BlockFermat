def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩
#align mul_action.to_perm MulAction.toPerm

def MulAction.toPermHom : α →* Equiv.Perm β where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂
#align mul_action.to_perm_hom MulAction.toPermHom

def AddAction.toPermHom (α : Type*) [AddGroup α] [AddAction α β] :
    α →+ Additive (Equiv.Perm β) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom (Multiplicative α) β
#align add_action.to_perm_hom AddAction.toPermHom

def {α : Type*} (f : Equiv.Perm α) (a : α) : f • a = f a :=
  rfl
#align equiv.perm.smul_def Equiv.Perm.smul_def

def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Function.Bijective (a • · : β → β) :=
  MulAction.bijective <| Units.mk0 a ha
#align mul_action.bijective₀ MulAction.bijective₀

def DistribMulAction.toAddEquiv (x : α) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x, MulAction.toPermHom α β x with }
#align distrib_mul_action.to_add_equiv DistribMulAction.toAddEquiv

def DistribMulAction.toAddAut : α →* AddAut β where
  toFun := DistribMulAction.toAddEquiv β
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
#align distrib_mul_action.to_add_aut DistribMulAction.toAddAut

def DistribMulAction.toAddEquiv₀ {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
    [DistribMulAction α β] (x : α) (hx : x ≠ 0) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x with
    invFun := fun b ↦ x⁻¹ • b
    left_inv := fun b ↦ inv_smul_smul₀ hx b
    right_inv := fun b ↦ smul_inv_smul₀ hx b }

variable {α β}

theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩
#align smul_eq_zero_iff_eq smul_eq_zero_iff_eq

def MulDistribMulAction.toMulEquiv (x : α) : β ≃* β :=
  { MulDistribMulAction.toMonoidHom β x, MulAction.toPermHom α β x with }
#align mul_distrib_mul_action.to_mul_equiv MulDistribMulAction.toMulEquiv

def MulDistribMulAction.toMulAut : α →* MulAut β where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)
#align mul_distrib_mul_action.to_mul_aut MulDistribMulAction.toMulAut

def arrowAction {G A B : Type*} [DivisionMonoid G] [MulAction G A] : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul := by
    intro f
    show (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul := by
    intros x y f
    show (fun a => f ((x*y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]
#align arrow_action arrowAction

def arrowMulDistribMulAction {G A B : Type*} [Group G] [MulAction G A] [Monoid B] :
    MulDistribMulAction G (A → B) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl
#align arrow_mul_distrib_mul_action arrowMulDistribMulAction

def mulAutArrow {G A H} [Group G] [MulAction G A] [Monoid H] : G →* MulAut (A → H) :=
  MulDistribMulAction.toMulAut _ _
#align mul_aut_arrow mulAutArrow