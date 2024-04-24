def conGen [Mul M] (r : M → M → Prop) : Con M :=
  ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩
#align con_gen conGen

def mulKer (f : M → P) (h : ∀ x y, f (x * y) = f x * f y) : Con M
    where
  toSetoid := Setoid.ker f
  mul' h1 h2 := by
    dsimp [Setoid.ker, onFun] at *
    rw [h, h1, h2, h]
#align con.mul_ker Con.mulKer

def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }
#align con.prod Con.prod

def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }
#align con.pi Con.pi

def Quotient :=
  Quotient c.toSetoid
#align con.quotient Con.Quotient

def toQuotient : M → c.Quotient :=
  Quotient.mk''

variable (c)

-- Porting note: was `priority 0`. why?
/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive "Coercion from a type with an addition to its quotient by an additive congruence
relation"]
instance (priority := 10) : CoeTC M c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive "The quotient by a decidable additive congruence relation has decidable equality."]
instance (priority := 500) [∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[to_additive (attr := simp)]
theorem quot_mk_eq_coe {M : Type*} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align con.quot_mk_eq_coe Con.quot_mk_eq_coe

def liftOn {β} {c : Con M} (q : c.Quotient) (f : M → β) (h : ∀ a b, c a b → f a = f b) :
    β :=
  Quotient.liftOn' q f h
#align con.lift_on Con.liftOn

def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M → M → β)
    (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h
#align con.lift_on₂ Con.liftOn₂

def hrecOn₂ {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort*}
    (a : cM.Quotient) (b : cN.Quotient) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → HEq (f x y) (f x' y')) : φ a b :=
  Quotient.hrecOn₂' a b f h
#align con.hrec_on₂ Con.hrecOn₂

def congr {c d : Con M} (h : c = d) : c.Quotient ≃* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply ext_iff.2 h with
    map_mul' := fun x y => by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }
#align con.congr Con.congr

def {c d : Con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl
#align con.le_def Con.le_def

def AddCon.le_def

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type with
an addition."]
instance : InfSet (Con M) where
  sInf S :=
    { r := fun x y => ∀ c : Con M, c ∈ S → c x y
      iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm <| h c hc,
        fun h1 h2 c hc => c.trans (h1 c hc) <| h2 c hc⟩
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of
the set's image under the map to the underlying equivalence relation."]
theorem sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S) :=
  Setoid.ext' fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩
#align con.Inf_to_setoid Con.sInf_toSetoid

def Con.coe_sInf
#align add_con.Inf_def AddCon.coe_sInf

def Con.coe_inf
#align add_con.inf_def AddCon.coe_inf

def {c d : Con M} : c ⊔ d = conGen (⇑c ⊔ ⇑d) := by rw [sup_eq_conGen]; rfl
#align con.sup_def Con.sup_def

def AddCon.sup_def

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
@[to_additive sSup_eq_addConGen "The supremum of a set of additive congruence relations `S` equals
the smallest additive congruence relation containing the binary relation 'there exists `c ∈ S`
such that `x` is related to `y` by `c`'."]
theorem sSup_eq_conGen (S : Set (Con M)) :
    sSup S = conGen fun x y => ∃ c : Con M, c ∈ S ∧ c x y := by
  rw [conGen_eq]
  apply congr_arg sInf
  ext
  exact ⟨fun h _ _ ⟨r, hr⟩ => h hr.1 hr.2, fun h r hS _ _ hr => h _ _ ⟨r, hS, hr⟩⟩
#align con.Sup_eq_con_gen Con.sSup_eq_conGen

def {S : Set (Con M)} :
    sSup S = conGen (sSup ((⇑) '' S)) := by
  rw [sSup_eq_conGen, sSup_image]
  congr with (x y)
  simp only [sSup_image, iSup_apply, iSup_Prop_eq, exists_prop, rel_eq_coe]
#align con.Sup_def Con.sSup_def

def AddCon.sSup_def

variable (M)

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
@[to_additive "There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`."]
protected def gi : @GaloisInsertion (M → M → Prop) (Con M) _ _ conGen DFunLike.coe
    where
  choice r _ := conGen r
  gc _ c := ⟨fun H _ _ h => H <| ConGen.Rel.of _ _ h, @fun H => conGen_of_con c ▸ conGen_mono H⟩
  le_l_u x := (conGen_of_con x).symm ▸ le_refl x
  choice_eq _ _ := rfl
#align con.gi Con.gi

def mapGen (f : M → N) : Con N :=
  conGen fun x y => ∃ a b, f a = x ∧ f b = y ∧ c a b
#align con.map_gen Con.mapGen

def mapOfSurjective (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (h : mulKer f H ≤ c)
    (hf : Surjective f) : Con N :=
  { c.toSetoid.mapOfSurjective f h hf with
    mul' := fun h₁ h₂ => by
      rcases h₁ with ⟨a, b, rfl, rfl, h1⟩
      rcases h₂ with ⟨p, q, rfl, rfl, h2⟩
      exact ⟨a * p, b * q, by rw [H], by rw [H], c.mul h1 h2⟩ }
#align con.map_of_surjective Con.mapOfSurjective

def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }
#align con.comap Con.comap

def correspondence : { d // c ≤ d } ≃o Con c.Quotient
    where
  toFun d :=
    d.1.mapOfSurjective (↑) _ (by rw [mul_ker_mk_eq]; exact d.2) <|
      @Quotient.exists_rep _ c.toSetoid
  invFun d :=
    ⟨comap ((↑) : M → c.Quotient) (fun x y => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      Subtype.ext_iff_val.2 <|
        ext fun x y =>
          ⟨fun h =>
            let ⟨a, b, hx, hy, H⟩ := h
            d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) <| d.1.trans H <| d.2 <| c.eq.1 hy,
            fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      ext fun x y =>
        ⟨fun h =>
          let ⟨_, _, hx, hy, H⟩ := h
          hx ▸ hy ▸ H,
          Con.induction_on₂ x y fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' := @fun s t => by
    constructor
    · intros h x y hs
      rcases h ⟨x, y, rfl, rfl, hs⟩ with ⟨a, b, hx, hy, ht⟩
      exact t.1.trans (t.1.symm <| t.2 <| Quotient.eq_rel.1 hx)
        (t.1.trans ht (t.2 <| Quotient.eq_rel.1 hy))
    · intros h _ _ hs
      rcases hs with ⟨a, b, hx, hy, Hs⟩
      exact ⟨a, b, hx, hy, h Hs⟩
#align con.correspondence Con.correspondence

def submonoid : Submonoid (M × M)
    where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul
#align con.submonoid Con.submonoid

def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M
    where
  r x y := (x, y) ∈ N
  iseqv := H
  mul' := N.mul_mem
#align con.of_submonoid Con.ofSubmonoid

def ker (f : M →* P) : Con M :=
  mulKer f (map_mul f)
#align con.ker Con.ker

def mk' : M →* c.Quotient :=
  { toFun := (↑)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
#align con.mk' Con.mk'

def lift (H : c ≤ ker f) : c.Quotient →* P
    where
  toFun x := (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]
#align con.lift Con.lift

def kerLift : (ker f).Quotient →* P :=
  ((ker f).lift f) fun _ _ => id
#align con.ker_lift Con.kerLift

def map (c d : Con M) (h : c ≤ d) : c.Quotient →* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc
#align con.map Con.map

def quotientKerEquivRange (f : M →* P) : (ker f).Quotient ≃* MonoidHom.mrange f :=
  { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.submonoidCongr kerLift_range_eq)).comp
        ⟨fun x y h =>
          kerLift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩; rfl⟩⟩) with
    map_mul' := MonoidHom.map_mul _ }
#align con.quotient_ker_equiv_range Con.quotientKerEquivRange

def quotientKerEquivOfRightInverse (f : M →* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by conv_rhs => rw [← hf x]; rfl }
#align con.quotient_ker_equiv_of_right_inverse Con.quotientKerEquivOfRightInverse

def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec
#align con.quotient_ker_equiv_of_surjective Con.quotientKerEquivOfSurjective

def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
  (Con.congr comap_eq).trans <| quotientKerEquivRange <| c.mk'.comp f
#align con.comap_quotient_equiv Con.comapQuotientEquiv

def quotientQuotientEquivQuotient (c d : Con M) (h : c ≤ d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }
#align con.quotient_quotient_equiv_quotient Con.quotientQuotientEquivQuotient

def liftOnUnits (u : Units c.Quotient) (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx',
      c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx') : α := by
  refine'
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 → y * x = 1 → α) (u : c.Quotient)
      (↑u⁻¹ : c.Quotient)
      (fun (x y : M) (hxy : (x * y : c.Quotient) = 1) (hyx : (y * x : c.Quotient) = 1) =>
        f x y (c.eq.1 hxy) (c.eq.1 hyx))
      (fun x y x' y' hx hy => _) u.3 u.4
  refine' Function.hfunext _ _
  rw [c.eq.2 hx, c.eq.2 hy]
  · rintro Hxy Hxy' -
    refine' Function.hfunext _ _
    · rw [c.eq.2 hx, c.eq.2 hy]
    · rintro Hyx Hyx' -
      exact heq_of_eq (Hf _ _ _ _ _ _ _ _ hx hy)
#align con.lift_on_units Con.liftOnUnits

structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

structure AddCon [Add M] extends Setoid M where
  /-- Additive congruence relations are closed under addition -/
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
#align add_con AddCon

structure Con [Mul M] extends Setoid M where
  /-- Congruence relations are closed under multiplication -/
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
#align con Con