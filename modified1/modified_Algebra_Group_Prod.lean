def [Mul M] [Mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) :=
  rfl
#align prod.mul_def Prod.mul_def

def Prod.add_def

@[to_additive]
theorem one_mk_mul_one_mk [Monoid M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) :=
  by rw [mk_mul_mk, mul_one]
#align prod.one_mk_mul_one_mk Prod.one_mk_mul_one_mk

def fst : M × N →ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩
#align mul_hom.fst MulHom.fst

def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩
#align mul_hom.snd MulHom.snd

def prod (f : M →ₙ* N) (g : M →ₙ* P) :
    M →ₙ* N × P where
  toFun := Pi.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)
#align mul_hom.prod MulHom.prod

def prodMap : M × N →ₙ* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))
#align mul_hom.prod_map MulHom.prodMap

def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl
#align mul_hom.prod_map_def MulHom.prodMap_def

def AddHom.prodMap_def

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align mul_hom.coe_prod_map MulHom.coe_prodMap

def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align mul_hom.coprod MulHom.coprod

def fst : M × N →* M :=
  { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }
#align monoid_hom.fst MonoidHom.fst

def snd : M × N →* N :=
  { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }
#align monoid_hom.snd MonoidHom.snd

def inl : M →* M × N :=
  { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }
#align monoid_hom.inl MonoidHom.inl

def inr : N →* M × N :=
  { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }
#align monoid_hom.inr MonoidHom.inr

def prod (f : M →* N) (g : M →* P) :
    M →* N × P where
  toFun := Pi.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)
#align monoid_hom.prod MonoidHom.prod

def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))
#align monoid_hom.prod_map MonoidHom.prodMap

def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl
#align monoid_hom.prod_map_def MonoidHom.prodMap_def

def AddMonoidHom.prodMap_def

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align monoid_hom.coe_prod_map MonoidHom.coe_prodMap

def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align monoid_hom.coprod MonoidHom.coprod

def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }
#align mul_equiv.prod_comm MulEquiv.prodComm

def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }
#align mul_equiv.prod_prod_prod_comm MulEquiv.prodProdProdComm

def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (f.map_mul _ _) (g.map_mul _ _) }
#align mul_equiv.prod_congr MulEquiv.prodCongr

def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }
#align mul_equiv.unique_prod MulEquiv.uniqueProd

def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }
#align mul_equiv.prod_unique MulEquiv.prodUnique

def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ where
  toFun := (Units.map (MonoidHom.fst M N)).prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right_inv := fun ⟨u₁, u₂⟩ => by
    simp only [Units.map, MonoidHom.coe_fst, Units.inv_eq_val_inv,
      MonoidHom.coe_snd, MonoidHom.prod_apply, Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  map_mul' := MonoidHom.map_mul _
#align mul_equiv.prod_units MulEquiv.prodUnits

def embedProduct (α : Type*) [Monoid α] : αˣ →* α × αᵐᵒᵖ where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, eq_self_iff_true, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]
#align units.embed_product Units.embedProduct

def mulMulHom [CommSemigroup α] :
    α × α →ₙ* α where
  toFun a := a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _
#align mul_mul_hom mulMulHom

def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }
#align mul_monoid_hom mulMonoidHom

def mulMonoidWithZeroHom [CommMonoidWithZero α] : α × α →*₀ α :=
  { mulMonoidHom with map_zero' := mul_zero _ }
#align mul_monoid_with_zero_hom mulMonoidWithZeroHom

def divMonoidHom [DivisionCommMonoid α] : α × α →* α where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _
#align div_monoid_hom divMonoidHom

def divMonoidWithZeroHom [CommGroupWithZero α] : α × α →*₀ α where
  toFun a := a.1 / a.2
  map_zero' := zero_div _
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _
#align div_monoid_with_zero_hom divMonoidWithZeroHom