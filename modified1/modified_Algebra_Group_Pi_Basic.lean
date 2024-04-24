def [∀ i, One <| f i] : (1 : ∀ i, f i) = fun _ => 1 :=
  rfl
#align pi.one_def Pi.one_def

def Pi.zero_def

@[to_additive (attr := simp)] lemma _root_.Function.const_one [One β] : const α (1 : β) = 1 := rfl
#align pi.const_one Function.const_one

def [∀ i, Mul <| f i] : x * y = fun i => x i * y i :=
  rfl
#align pi.mul_def Pi.mul_def

def Pi.add_def

@[to_additive (attr := simp)]
lemma _root_.Function.const_mul [Mul β] (a b : β) : const α a * const α b = const α (a * b) := rfl
#align pi.const_mul Function.const_mul

def [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) : x ^ b = fun i => x i ^ b :=
  rfl
#align pi.pow_def Pi.pow_def

def Pi.smul_def
#align pi.vadd_def Pi.vadd_def

def [∀ i, Inv <| f i] : x⁻¹ = fun i => (x i)⁻¹ :=
  rfl
#align pi.inv_def Pi.inv_def

def Pi.neg_def

@[to_additive]
lemma _root_.Function.const_inv [Inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ := rfl
#align pi.const_inv Function.const_inv

def [∀ i, Div <| f i] : x / y = fun i => x i / y i :=
  rfl
#align pi.div_def Pi.div_def

def Pi.sub_def

@[to_additive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl
#align pi.div_comp Pi.div_comp

def mulSingle (i : I) (x : f i) : ∀ (j : I), f j :=
  Function.update 1 i x
#align pi.mul_single Pi.mulSingle

def prod (f' : ∀ i, f i) (g' : ∀ i, g i) (i : I) : f i × g i :=
  (f' i, g' i)
#align pi.prod Pi.prod

def uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)
#align unique_of_surjective_one uniqueOfSurjectiveOne