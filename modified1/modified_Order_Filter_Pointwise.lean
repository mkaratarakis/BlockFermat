def instOne : One (Filter α) :=
  ⟨pure 1⟩
#align filter.has_one Filter.instOne

def pureOneHom : OneHom α (Filter α) where
  toFun := pure; map_one' := pure_one
#align filter.pure_one_hom Filter.pureOneHom

def instInvolutiveInv : InvolutiveInv (Filter α) :=
  { Filter.instInv with
    inv_inv := fun f => map_map.trans <| by rw [inv_involutive.comp_self, map_id] }
#align filter.has_involutive_inv Filter.instInvolutiveInv

def instMul : Mul (Filter α) :=
  ⟨/- This is defeq to `map₂ (· * ·) f g`, but the hypothesis unfolds to `t₁ * t₂ ⊆ s` rather
  than all the way to `Set.image2 (· * ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· * ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ * t₂ ⊆ s } }⟩
#align filter.has_mul Filter.instMul

def pureMulHom : α →ₙ* Filter α where
  toFun := pure; map_mul' _ _ := pure_mul_pure.symm
#align filter.pure_mul_hom Filter.pureMulHom

def instDiv : Div (Filter α) :=
  ⟨/- This is defeq to `map₂ (· / ·) f g`, but the hypothesis unfolds to `t₁ / t₂ ⊆ s`
  rather than all the way to `Set.image2 (· / ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· / ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ / t₂ ⊆ s } }⟩
#align filter.has_div Filter.instDiv

def instNSMul [Zero α] [Add α] : SMul ℕ (Filter α) :=
  ⟨nsmulRec⟩
#align filter.has_nsmul Filter.instNSMul

def instNPow [One α] [Mul α] : Pow (Filter α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align filter.has_npow Filter.instNPow

def instZSMul [Zero α] [Add α] [Neg α] : SMul ℤ (Filter α) :=
  ⟨zsmulRec⟩
#align filter.has_zsmul Filter.instZSMul

def instZPow [One α] [Mul α] [Inv α] : Pow (Filter α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩
#align filter.has_zpow Filter.instZPow

def semigroup [Semigroup α] : Semigroup (Filter α) where
  mul := (· * ·)
  mul_assoc _ _ _ := map₂_assoc mul_assoc
#align filter.semigroup Filter.semigroup

def commSemigroup [CommSemigroup α] : CommSemigroup (Filter α) :=
  { Filter.semigroup with mul_comm := fun _ _ => map₂_comm mul_comm }
#align filter.comm_semigroup Filter.commSemigroup

def mulOneClass : MulOneClass (Filter α) where
  one := 1
  mul := (· * ·)
  one_mul := map₂_left_identity one_mul
  mul_one := map₂_right_identity mul_one
#align filter.mul_one_class Filter.mulOneClass

def mapMonoidHom [MonoidHomClass F α β] (φ : F) : Filter α →* Filter β where
  toFun := map φ
  map_one' := Filter.map_one φ
  map_mul' _ _ := Filter.map_mul φ
#align filter.map_monoid_hom Filter.mapMonoidHom

def pureMonoidHom : α →* Filter α :=
  { pureMulHom, pureOneHom with }
#align filter.pure_monoid_hom Filter.pureMonoidHom

def monoid : Monoid (Filter α) :=
  { Filter.mulOneClass, Filter.semigroup, @Filter.instNPow α _ _ with }
#align filter.monoid Filter.monoid

def commMonoid [CommMonoid α] : CommMonoid (Filter α) :=
  { Filter.mulOneClass, Filter.commSemigroup with }
#align filter.comm_monoid Filter.commMonoid

def divisionMonoid : DivisionMonoid (Filter α) :=
  { Filter.monoid, Filter.instInvolutiveInv, Filter.instDiv, Filter.instZPow (α := α) with
    mul_inv_rev := fun s t => map_map₂_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Filter.mul_eq_one_iff.1 h
      rw [inv_pure, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun f g => map_map₂_distrib_right div_eq_mul_inv }
#align filter.division_monoid Filter.divisionMonoid

def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Filter α) :=
  { Filter.divisionMonoid, Filter.commSemigroup with }
#align filter.division_comm_monoid Filter.divisionCommMonoid

def instDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Filter α) :=
  { Filter.instInvolutiveNeg with
    neg_mul := fun _ _ => map₂_map_left_comm neg_mul
    mul_neg := fun _ _ => map_map₂_right_comm mul_neg }
#align filter.has_distrib_neg Filter.instDistribNeg

def instSMul : SMul (Filter α) (Filter β) :=
  ⟨/- This is defeq to `map₂ (· • ·) f g`, but the hypothesis unfolds to `t₁ • t₂ ⊆ s`
  rather than all the way to `Set.image2 (· • ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· • ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ • t₂ ⊆ s } }⟩
#align filter.has_smul Filter.instSMul

def instVSub : VSub (Filter α) (Filter β) :=
  ⟨/- This is defeq to `map₂ (-ᵥ) f g`, but the hypothesis unfolds to `t₁ -ᵥ t₂ ⊆ s` rather than all
  the way to `Set.image2 (-ᵥ) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· -ᵥ ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ -ᵥ t₂ ⊆ s } }⟩
#align filter.has_vsub Filter.instVSub

def instSMulFilter : SMul α (Filter β) :=
  ⟨fun a => map (a • ·)⟩
#align filter.has_smul_filter Filter.instSMulFilter

def mulAction [Monoid α] [MulAction α β] : MulAction (Filter α) (Filter β) where
  one_smul f := map₂_pure_left.trans <| by simp_rw [one_smul, map_id']
  mul_smul f g h := map₂_assoc mul_smul
#align filter.mul_action Filter.mulAction

def mulActionFilter [Monoid α] [MulAction α β] : MulAction α (Filter β) where
  mul_smul a b f := by simp only [← Filter.map_smul, map_map, Function.comp, ← mul_smul]
  one_smul f := by simp only [← Filter.map_smul, one_smul, map_id']
#align filter.mul_action_filter Filter.mulActionFilter

def distribMulActionFilter [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Filter β) where
  smul_add _ _ _ := map_map₂_distrib <| smul_add _
  smul_zero _ := (map_pure _ _).trans <| by rw [smul_zero, pure_zero]
#align filter.distrib_mul_action_filter Filter.distribMulActionFilter

def mulDistribMulActionFilter [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]
#align filter.mul_distrib_mul_action_filter Filter.mulDistribMulActionFilter