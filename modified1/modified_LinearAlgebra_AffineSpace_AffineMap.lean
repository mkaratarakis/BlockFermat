def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p
#align linear_map.to_affine_map LinearMap.toAffineMap

def const (p : P2) : P1 →ᵃ[k] P2 where
  toFun := Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp
#align affine_map.const AffineMap.const

def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
    P1 →ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]
#align affine_map.mk' AffineMap.mk'

def fst : P1 × P2 →ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl
#align affine_map.fst AffineMap.fst

def snd : P1 × P2 →ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl
#align affine_map.snd AffineMap.snd

def id : P1 →ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' _ _ := rfl
#align affine_map.id AffineMap.id

def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply, g.map_vadd, f.map_vadd]
    rfl
#align affine_map.comp AffineMap.comp

def linearHom : (P1 →ᵃ[k] P1) →* V1 →ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl
#align affine_map.linear_hom AffineMap.linearHom

def lineMap (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
  ((LinearMap.id : k →ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀
#align affine_map.line_map AffineMap.lineMap

def proj (i : ι) : (∀ i : ι, P i) →ᵃ[k] P i where
  toFun f := f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl
#align affine_map.proj AffineMap.proj

def toConstProdLinearMap : (V1 →ᵃ[k] V2) ≃ₗ[R] V2 × (V1 →ₗ[k] V2) where
  toFun f := ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp [const_apply _ _]  -- Porting note: `simp` needs `_`s to use this lemma
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_apply _ _, const_linear _ _]  -- Porting note: `simp` needs `_`s
  map_add' := by simp
  map_smul' := by simp
#align affine_map.to_const_prod_linear_map AffineMap.toConstProdLinearMap

def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c
#align affine_map.homothety AffineMap.homothety

def (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl
#align affine_map.homothety_def AffineMap.homothety_def

def homothetyHom (c : P1) : k →* P1 →ᵃ[k] P1 where
  toFun := homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c
#align affine_map.homothety_hom AffineMap.homothetyHom

def homothetyAffine (c : P1) : k →ᵃ[k] P1 →ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩
#align affine_map.homothety_affine AffineMap.homothetyAffine

structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  toFun : P1 → P2
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p
#align affine_map AffineMap