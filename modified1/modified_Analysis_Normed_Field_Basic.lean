def normHom : α →*₀ ℝ where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul
#align norm_hom normHom

def nnnormHom : α →*₀ ℝ≥0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul
#align nnnorm_hom nnnormHom

def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulLeft₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulRight₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
lemma comap_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma comap_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulRight a ha)

@[simp]
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le
#align filter.tendsto_mul_left_cobounded Filter.tendsto_mul_left_cobounded

def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_lt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact one_lt_inv (norm_pos_iff.2 hx) hlt
    · exact ⟨x, hlt⟩

instance Real.normedCommRing : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul := fun x y => (abs_mul x y).le }

noncomputable instance Real.normedField : NormedField ℝ :=
  { Real.normedAddCommGroup, Real.field with
    norm_mul' := abs_mul }

noncomputable instance Real.denselyNormedField : DenselyNormedField ℝ where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]
#align real.to_nnreal_mul_nnnorm Real.toNNReal_mul_nnnorm

def NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R :=
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul := fun x y => by
      show ‖f (x * y)‖ ≤ ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }
#align non_unital_semi_normed_ring.induced NonUnitalSeminormedRing.induced

def NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align non_unital_normed_ring.induced NonUnitalNormedRing.induced

def SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }
#align semi_normed_ring.induced SeminormedRing.induced

def NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }
#align normed_ring.induced NormedRing.induced

def NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

/-- An injective non-unital ring homomorphism from a `NonUnitalCommRing` to a
`NonUnitalNormedCommRing` induces a `NonUnitalNormedCommRing` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedCommRing R :=
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }
/-- A non-unital ring homomorphism from a `CommRing` to a `SeminormedRing` induces a
`SeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }
#align semi_normed_comm_ring.induced SeminormedCommRing.induced

def NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_comm_ring.induced NormedCommRing.induced

def NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S] [NonUnitalRingHomClass F R S]
    (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul' := fun x y => by
      show ‖f (x * y)‖ = ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }
#align normed_division_ring.induced NormedDivisionRing.induced

def NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }
#align normed_field.induced NormedField.induced

structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul := fun x y =>
      calc
        ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
        _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
        _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
          (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
        _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
        _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
          apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
        _ = ‖x‖ * ‖y‖ := rfl
         }
#align prod.non_unital_semi_normed_ring Prod.nonUnitalSeminormedRing

structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (π i)] : NonUnitalSeminormedRing (∀ i, π i) :=
  { Pi.seminormedAddCommGroup, Pi.nonUnitalRing with
    norm_mul := fun x y =>
      NNReal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ‖x i * y i‖₊) ≤
              Finset.univ.sup ((fun i => ‖x i‖₊) * fun i => ‖y i‖₊) :=
            Finset.sup_mono_fun fun _ _ => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ‖x i‖₊) * Finset.univ.sup fun i => ‖y i‖₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg _ (fun _ _ => zero_le _) fun _ _ => zero_le _
           }
#align pi.non_unital_semi_normed_ring Pi.nonUnitalSeminormedRing

structure on the product of two seminormed rings,
  using the sup norm. -/
instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { nonUnitalSeminormedRing, instRing with }
#align prod.semi_normed_ring Prod.seminormedRing

structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.seminormedRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (π i)] :
    SeminormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }
#align pi.semi_normed_ring Pi.seminormedRing

structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }
#align prod.non_unital_normed_ring Prod.nonUnitalNormedRing

structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type*} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }
#align pi.non_unital_normed_ring Pi.nonUnitalNormedRing

structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { nonUnitalNormedRing, instRing with }
#align prod.normed_ring Prod.normedRing

structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type*} [Fintype ι] [∀ i, NormedRing (π i)] :
    NormedRing (∀ i, π i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }
#align pi.normed_ring Pi.normedRing

structure on the product of two non-unital seminormed
commutative rings, using the sup norm. -/
instance Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing (α × β) :=
  { nonUnitalSeminormedRing, instNonUnitalCommRing with }

/-- Non-unital seminormed commutative ring structure on the product of finitely many non-unital
seminormed commutative rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedCommRing (π i)] : NonUnitalSeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

instance MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- A non-unital subalgebra of a non-unital seminormed commutative ring is also a non-unital
seminormed commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

/-- A non-unital subalgebra of a non-unital normed commutative ring is also a non-unital normed
commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

/-- Non-unital normed commutative ring structure on the product of two non-unital normed
commutative rings, using the sup norm. -/
instance Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

/-- Normed commutative ring structure on the product of finitely many non-unital normed
commutative rings, using the sup norm. -/
instance Pi.nonUnitalNormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalNormedCommRing (π i)] : NonUnitalNormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

/-- Seminormed commutative ring structure on the product of two seminormed commutative rings,
  using the sup norm. -/
instance Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, instCommRing with }

/-- Seminormed commutative ring structure on the product of finitely many seminormed commutative
rings, using the sup norm. -/
instance Pi.seminormedCommRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedCommRing (π i)] :
    SeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

instance MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

end SeminormedCommRing

section NormedCommRing

/-- A subalgebra of a seminormed commutative ring is also a seminormed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

/-- A subalgebra of a normed commutative ring is also a normed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]

instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

/-- Normed commutative ring structure on the product of two normed commutative rings, using the sup
norm. -/
instance Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β) :=
  { nonUnitalNormedRing, instCommRing with }

/-- Normed commutative ring structure on the product of finitely many normed commutative rings,
using the sup norm. -/
instance Pi.normedCommutativeRing {π : ι → Type*} [Fintype ι] [∀ i, NormedCommRing (π i)] :
    NormedCommRing (∀ i, π i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where
  __ := instNormedRing
  __ := instSeminormedCommRing

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_sub_tendsto_zero.2 <| by
        have : ∀ e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [_root_.mul_sub, _root_.sub_mul, sub_add_sub_cancel]
            -- Porting note: `ENNReal.{mul_sub, sub_mul}` should be protected
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        -- Porting note: `show` used to select a goal to work on
        rotate_right
        show Tendsto _ _ _
        exact tendsto_const_nhds
        simp⟩
#align semi_normed_ring_top_monoid semi_normed_ring_top_monoid

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R :=
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul := fun x y => by
      show ‖f (x * y)‖ ≤ ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }
#align non_unital_semi_normed_ring.induced NonUnitalSeminormedRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align non_unital_normed_ring.induced NonUnitalNormedRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }
#align semi_normed_ring.induced SeminormedRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }
#align normed_ring.induced NormedRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

/-- An injective non-unital ring homomorphism from a `NonUnitalCommRing` to a
`NonUnitalNormedCommRing` induces a `NonUnitalNormedCommRing` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedCommRing R :=
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }
/-- A non-unital ring homomorphism from a `CommRing` to a `SeminormedRing` induces a
`SeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }
#align semi_normed_comm_ring.induced SeminormedCommRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_comm_ring.induced NormedCommRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S] [NonUnitalRingHomClass F R S]
    (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul' := fun x y => by
      show ‖f (x * y)‖ = ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }
#align normed_division_ring.induced NormedDivisionRing.induced

structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }
#align normed_field.induced NormedField.induced

structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  -- Porting note: is this `let` a bad idea somehow?
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }
#align norm_one_class.induced NormOneClass.induced