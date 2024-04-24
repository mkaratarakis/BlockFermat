def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_seminorm.le_def GroupSeminorm.le_def

def AddGroupSeminorm.le_def

@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_seminorm.lt_def GroupSeminorm.lt_def

def AddGroupSeminorm.lt_def

@[to_additive (attr := simp, norm_cast)]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_seminorm.coe_le_coe GroupSeminorm.coe_le_coe

def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F
    where
  toFun x := p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
  mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le <| map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]
#align group_seminorm.comp GroupSeminorm.comp

def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_seminorm.le_def NonarchAddGroupSeminorm.le_def

def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_seminorm.lt_def NonarchAddGroupSeminorm.lt_def

def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_norm.le_def GroupNorm.le_def

def AddGroupNorm.le_def

@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_norm.lt_def GroupNorm.lt_def

def AddGroupNorm.lt_def

@[to_additive (attr := simp, norm_cast)]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_norm.coe_le_coe GroupNorm.coe_le_coe

def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_norm.le_def NonarchAddGroupNorm.le_def

def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_norm.lt_def NonarchAddGroupNorm.lt_def

structure AddGroupSeminorm (G : Type*) [AddGroup G] where
  -- Porting note: can't extend `ZeroHom G ℝ` because otherwise `to_additive` won't work since
  -- we aren't using old structures
  /-- The bare function of an `AddGroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of zero is zero. -/
  protected map_zero' : toFun 0 = 0
  /-- The seminorm is subadditive. -/
  protected add_le' : ∀ r s, toFun (r + s) ≤ toFun r + toFun s
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r
#align add_group_seminorm AddGroupSeminorm

structure GroupSeminorm (G : Type*) [Group G] where
  /-- The bare function of a `GroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of one is zero. -/
  protected map_one' : toFun 1 = 0
  /-- The seminorm applied to a product is dominated by the sum of the seminorm applied to the
  factors. -/
  protected mul_le' : ∀ x y, toFun (x * y) ≤ toFun x + toFun y
  /-- The seminorm is invariant under inversion. -/
  protected inv' : ∀ x, toFun x⁻¹ = toFun x
#align group_seminorm GroupSeminorm

structure NonarchAddGroupSeminorm (G : Type*) [AddGroup G] extends ZeroHom G ℝ where
  /-- The seminorm applied to a sum is dominated by the maximum of the function applied to the
  addends. -/
  protected add_le_max' : ∀ r s, toFun (r + s) ≤ max (toFun r) (toFun s)
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r
#align nonarch_add_group_seminorm NonarchAddGroupSeminorm

structure AddGroupNorm (G : Type*) [AddGroup G] extends AddGroupSeminorm G where
  /-- If the image under the seminorm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
#align add_group_norm AddGroupNorm

structure GroupNorm (G : Type*) [Group G] extends GroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is one. -/
  protected eq_one_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 1
#align group_norm GroupNorm

structure NonarchAddGroupNorm (G : Type*) [AddGroup G] extends NonarchAddGroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
#align nonarch_add_group_norm NonarchAddGroupNorm