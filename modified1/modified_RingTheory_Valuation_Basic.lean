def toPreorder : Preorder R :=
  Preorder.lift v
#align valuation.to_preorder Valuation.toPreorder

def comap {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp only [comp_apply, map_add, f.map_add] }
#align valuation.comap Valuation.comap

def map (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) ≤ f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }
#align valuation.map Valuation.map

def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s
#align valuation.is_equiv Valuation.IsEquiv

def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  carrier := { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_setOf, map_neg]
#align valuation.lt_add_subgroup Valuation.ltAddSubgroup

def supp : Ideal R where
  carrier := { x | v x = 0 }
  zero_mem' := map_zero v
  add_mem' {x y} hx hy := le_zero_iff.mp <|
    calc
      v (x + y) ≤ max (v x) (v y) := v.map_add x y
      _ ≤ 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _
#align valuation.supp Valuation.supp

def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)
#align add_valuation AddValuation

def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul
#align add_valuation.of AddValuation.of

def valuation : Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  v
#align add_valuation.valuation AddValuation.valuation

def asFun : R → Γ₀ := v

@[simp]
theorem map_mul : ∀ (x y : R), v (x * y) = v x + v y :=
  Valuation.map_mul v
#align add_valuation.map_mul AddValuation.map_mul

def toPreorder : Preorder R :=
  Preorder.lift v
#align add_valuation.to_preorder AddValuation.toPreorder

def comap {S : Type*} [Ring S] (f : S →+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  Valuation.comap f v
#align add_valuation.comap AddValuation.comap

def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) :
    AddValuation R Γ'₀ :=
  @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v
#align add_valuation.map AddValuation.map

def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  Valuation.IsEquiv v₁ v₂
#align add_valuation.is_equiv AddValuation.IsEquiv

def supp : Ideal R :=
  Valuation.supp v
#align add_valuation.supp AddValuation.supp

structure Valuation extends R →*₀ Γ₀ where
  /-- The valuation of a a sum is less that the sum of the valuations -/
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)
#align valuation Valuation