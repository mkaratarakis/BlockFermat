def rootsOfUnity (k : ℕ+) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ (k : ℕ) = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_setOf_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_setOf_eq, inv_pow, inv_one]
#align roots_of_unity rootsOfUnity

def rootsOfUnity.mkOfPowEq (ζ : M) {n : ℕ+} (h : ζ ^ (n : ℕ) = 1) : rootsOfUnity n M :=
  ⟨Units.ofPowEqOne ζ n h n.ne_zero, Units.pow_ofPowEqOne _ _⟩
#align roots_of_unity.mk_of_pow_eq rootsOfUnity.mkOfPowEq

def restrictRootsOfUnity [MonoidHomClass F R S] (σ : F) (n : ℕ+) :
    rootsOfUnity n R →* rootsOfUnity n S :=
  let h : ∀ ξ : rootsOfUnity n R, (σ (ξ : Rˣ)) ^ (n : ℕ) = 1 := fun ξ => by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, show (ξ : Rˣ) ^ (n : ℕ) = 1 from ξ.2, Units.val_one,
      map_one σ]
  { toFun := fun ξ =>
      ⟨@unitOfInvertible _ _ _ (invertibleOfPowEqOne _ _ (h ξ) n.ne_zero), by
        ext; rw [Units.val_pow_eq_pow_val]; exact h ξ⟩
    map_one' := by ext; exact map_one σ
    map_mul' := fun ξ₁ ξ₂ => by ext; rw [Subgroup.coe_mul, Units.val_mul]; exact map_mul σ _ _ }
#align restrict_roots_of_unity restrictRootsOfUnity

def MulEquiv.restrictRootsOfUnity (σ : R ≃* S) (n : ℕ+) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ n
  invFun := restrictRootsOfUnity σ.symm n
  left_inv ξ := by ext; exact σ.symm_apply_apply (ξ : Rˣ)
  right_inv ξ := by ext; exact σ.apply_symm_apply (ξ : Sˣ)
  map_mul' := (restrictRootsOfUnity _ n).map_mul
#align ring_equiv.restrict_roots_of_unity MulEquiv.restrictRootsOfUnity

def rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x ∈ nthRoots k (1 : R) } := by
  refine'
    { toFun := fun x => ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
      invFun := fun x => ⟨⟨x, ↑x ^ (k - 1 : ℕ), _, _⟩, _⟩
      left_inv := _
      right_inv := _ }
  pick_goal 4; · rintro ⟨x, hx⟩; ext; rfl
  pick_goal 4; · rintro ⟨x, hx⟩; ext; rfl
  all_goals
    rcases x with ⟨x, hx⟩; rw [mem_nthRoots k.pos] at hx
    simp only [Subtype.coe_mk, ← pow_succ, ← pow_succ', hx,
      tsub_add_cancel_of_le (show 1 ≤ (k : ℕ) from k.one_le)]
  · show (_ : Rˣ) ^ (k : ℕ) = 1
    simp only [Units.ext_iff, hx, Units.val_mk, Units.val_one, Subtype.coe_mk,
      Units.val_pow_eq_pow_val]
#align roots_of_unity_equiv_nth_roots rootsOfUnityEquivNthRoots

def IsPrimitiveRoot.iff_def

/-- Turn a primitive root μ into a member of the `rootsOfUnity` subgroup. -/
@[simps!]
def IsPrimitiveRoot.toRootsOfUnity {μ : M} {n : ℕ+} (h : IsPrimitiveRoot μ n) : rootsOfUnity n M :=
  rootsOfUnity.mkOfPowEq μ h.pow_eq_one
#align is_primitive_root.to_roots_of_unity IsPrimitiveRoot.toRootsOfUnity

def primitiveRoots (k : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  (nthRoots k (1 : R)).toFinset.filter fun ζ => IsPrimitiveRoot ζ k
#align primitive_roots primitiveRoots

def zmodEquivZPowers (h : IsPrimitiveRoot ζ k) : ZMod k ≃+ Additive (Subgroup.zpowers ζ) :=
  AddEquiv.ofBijective
    (AddMonoidHom.liftOfRightInverse (Int.castAddHom <| ZMod k) _ ZMod.int_cast_rightInverse
      ⟨{  toFun := fun i => Additive.ofMul (⟨_, i, rfl⟩ : Subgroup.zpowers ζ)
          map_zero' := by simp only [zpow_zero]; rfl
          map_add' := by intro i j; simp only [zpow_add]; rfl }, fun i hi => by
        simp only [AddMonoidHom.mem_ker, CharP.int_cast_eq_zero_iff (ZMod k) k, AddMonoidHom.coe_mk,
          Int.coe_castAddHom] at hi ⊢
        obtain ⟨i, rfl⟩ := hi
        simp [zpow_mul, h.pow_eq_one, one_zpow, zpow_natCast]⟩)
    (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro i hi
        rw [Subtype.ext_iff] at hi
        have := (h.zpow_eq_one_iff_dvd _).mp hi
        rw [← (CharP.int_cast_eq_zero_iff (ZMod k) k _).mpr this, eq_comm]
        exact ZMod.int_cast_rightInverse i
      · rintro ⟨ξ, i, rfl⟩
        refine' ⟨Int.castAddHom (ZMod k) i, _⟩
        rw [AddMonoidHom.liftOfRightInverse_comp_apply]
        rfl)
#align is_primitive_root.zmod_equiv_zpowers IsPrimitiveRoot.zmodEquivZPowers

def _root_.rootsOfUnityEquivOfPrimitiveRoots {S F} [CommRing S] [IsDomain S]
    [FunLike F R S] [MonoidHomClass F R S]
    {n : ℕ+} {f : F} (hf : Function.Injective f) (hζ : (primitiveRoots n R).Nonempty) :
    (rootsOfUnity n R) ≃* rootsOfUnity n S :=
  (Subgroup.equivMapOfInjective _ _ (Units.map_injective hf)).trans (MulEquiv.subgroupCongr
    (((mem_primitiveRoots (k := n) n.2).mp hζ.choose_spec).map_rootsOfUnity hf))

lemma _root_.rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    {S F} [CommRing S] [IsDomain S] [FunLike F R S] [MonoidHomClass F R S]
    {n : ℕ+} {f : F} (hf : Function.Injective f) (hζ : (primitiveRoots n R).Nonempty) (η) :
    f ((rootsOfUnityEquivOfPrimitiveRoots hf hζ).symm η : Rˣ) = (η : Sˣ) := by
  obtain ⟨ε, rfl⟩ := (rootsOfUnityEquivOfPrimitiveRoots hf hζ).surjective η
  rw [MulEquiv.symm_apply_apply, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe]

-- Porting note: rephrased the next few lemmas to avoid `∃ (Prop)`
theorem eq_pow_of_mem_rootsOfUnity {k : ℕ+} {ζ ξ : Rˣ} (h : IsPrimitiveRoot ζ k)
    (hξ : ξ ∈ rootsOfUnity k R) : ∃ (i : ℕ), i < k ∧ ζ ^ i = ξ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ζ ^ n = ξ := by rwa [← h.zpowers_eq] at hξ
  have hk0 : (0 : ℤ) < k := mod_cast k.pos
  let i := n % k
  have hi0 : 0 ≤ i := Int.emod_nonneg _ (ne_of_gt hk0)
  lift i to ℕ using hi0 with i₀ hi₀
  refine' ⟨i₀, _, _⟩
  · zify; rw [hi₀]; exact Int.emod_lt_of_pos _ hk0
  · rw [← zpow_natCast, hi₀, ← Int.emod_add_ediv n k, zpow_add, zpow_mul, h.zpow_eq_one, one_zpow,
      mul_one]
#align is_primitive_root.eq_pow_of_mem_roots_of_unity IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity

def autToPow : (S ≃ₐ[R] S) →* (ZMod n)ˣ :=
  let μ' := hμ.toRootsOfUnity
  have ho : orderOf μ' = n := by
    rw [hμ.eq_orderOf, ← hμ.val_toRootsOfUnity_coe, orderOf_units, Subgroup.orderOf_coe]
  MonoidHom.toHomUnits
    { toFun := fun σ => (map_rootsOfUnity_eq_pow_self σ.toAlgHom μ').choose
      map_one' := by
        dsimp only
        generalize_proofs h1
        have h := h1.choose_spec
        dsimp only [μ', AlgEquiv.one_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv] at *
        replace h : μ' = μ' ^ h1.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using h)
        nth_rw 1 [← pow_one μ'] at h
        rw [← Nat.cast_one, ZMod.nat_cast_eq_nat_cast_iff, ← ho, ← pow_eq_pow_iff_modEq, h]
      map_mul' := by
        intro x y
        dsimp only
        generalize_proofs hxy' hx' hy'
        have hxy := hxy'.choose_spec
        have hx := hx'.choose_spec
        have hy := hy'.choose_spec
        dsimp only [μ', AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.mul_apply] at *
        replace hxy : x (((μ' : Sˣ) : S) ^ hy'.choose) = ((μ' : Sˣ) : S) ^ hxy'.choose := hy ▸ hxy
        rw [x.map_pow] at hxy
        replace hxy : (((μ' : Sˣ) : S) ^ hx'.choose) ^ hy'.choose = ((μ' : Sˣ) : S) ^ hxy'.choose :=
          hx ▸ hxy
        rw [← pow_mul] at hxy
        replace hxy : μ' ^ (hx'.choose * hy'.choose) = μ' ^ hxy'.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using hxy)
        rw [← Nat.cast_mul, ZMod.nat_cast_eq_nat_cast_iff, ← ho, ← pow_eq_pow_iff_modEq, hxy] }
#align is_primitive_root.aut_to_pow IsPrimitiveRoot.autToPow

structure IsPrimitiveRoot (ζ : M) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ (k : ℕ) = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l
#align is_primitive_root IsPrimitiveRoot