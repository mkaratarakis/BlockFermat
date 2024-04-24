def orbit (a : α) :=
  Set.range fun m : M => m • a
#align mul_action.orbit MulAction.orbit

def fixedPoints : Set α :=
  { a : α | ∀ m : M, m • a = a }
#align mul_action.fixed_points MulAction.fixedPoints

def fixedBy (m : M) : Set α :=
  { x | m • x = x }
#align mul_action.fixed_by MulAction.fixedBy

def stabilizerSubmonoid (a : α) : Submonoid M where
  carrier := { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]
#align mul_action.stabilizer.submonoid MulAction.stabilizerSubmonoid

def FixedPoints.submonoid : Submonoid α where
  carrier := MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]
lemma FixedPoints.mem_submonoid (a : α) : a ∈ submonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end Monoid

section Group

variable [Group α] [MulDistribMulAction M α]

/-- The subgroup of elements fixed under the whole action. -/
def FixedPoints.subgroup : Subgroup α where
  __ := submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

/-- The notation for `FixedPoints.subgroup`, chosen to resemble `αᴹ`. -/
notation α "^*" M:51 => FixedPoints.subgroup M α

@[simp]
lemma FixedPoints.mem_subgroup (a : α) : a ∈ α^*M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma FixedPoints.subgroup_toSubmonoid : (α^*M).toSubmonoid = submonoid M α :=
  rfl

end Group

section AddMonoid

variable [AddMonoid α] [DistribMulAction M α]

/-- The additive submonoid of elements fixed under the whole action. -/
def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
lemma FixedPoints.mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end AddMonoid

section AddGroup

variable [AddGroup α] [DistribMulAction M α]

/-- The additive subgroup of elements fixed under the whole action. -/
def FixedPoints.addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

/-- The notation for `FixedPoints.addSubgroup`, chosen to resemble `αᴹ`. -/
notation α "^+" M:51 => FixedPoints.addSubgroup M α

@[simp]
lemma FixedPoints.mem_addSubgroup (a : α) : a ∈ α^+M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma FixedPoints.addSubgroup_toAddSubmonoid : (α^+M).toAddSubmonoid = addSubmonoid M α :=
  rfl

end AddGroup

end FixedPoints

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `NoZeroSMulDivisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type*} [Monoid M] [NonUnitalNonAssocRing R]
    [DistribMulAction M R] (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine' h _ _
  rw [smul_sub, h', sub_self]
#align smul_cancel_of_non_zero_divisor smul_cancel_of_non_zero_divisor

def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv :=
    ⟨mem_orbit_self, fun {a b} => by simp [orbit_eq_iff.symm, eq_comm], fun {a b} => by
      simp (config := { contextual := true }) [orbit_eq_iff.symm, eq_comm]⟩
#align mul_action.orbit_rel MulAction.orbitRel

def orbitRel.Quotient : Type _ :=
  _root_.Quotient <| orbitRel G α
#align mul_action.orbit_rel.quotient MulAction.orbitRel.Quotient

def orbitRel.Quotient.orbit (x : orbitRel.Quotient G α) : Set α :=
  Quotient.liftOn' x (orbit G) fun _ _ => MulAction.orbit_eq_iff.2
#align mul_action.orbit_rel.quotient.orbit MulAction.orbitRel.Quotient.orbit

def selfEquivSigmaOrbits' : α ≃ Σω : Ω, ω.orbit :=
  letI := orbitRel G α
  calc
    α ≃ Σω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm
#align mul_action.self_equiv_sigma_orbits' MulAction.selfEquivSigmaOrbits'

def selfEquivSigmaOrbits : α ≃ Σω : Ω, orbit G ω.out' :=
  (selfEquivSigmaOrbits' G α).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits MulAction.selfEquivSigmaOrbits

def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }
#align mul_action.stabilizer MulAction.stabilizer

def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : (orbitRel G α).Rel a b) :
    stabilizer G a ≃* stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g • b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer G b).symm
#align mul_action.stabilizer_equiv_stabilizer_of_orbit_rel MulAction.stabilizerEquivStabilizerOfOrbitRel

def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : (orbitRel G α).Rel a b) :
    stabilizer G a ≃+ stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g +ᵥ b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer G b).symm
#align add_action.stabilizer_equiv_stabilizer_of_orbit_rel AddAction.stabilizerEquivStabilizerOfOrbitRel