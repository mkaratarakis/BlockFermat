def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)
#align unique_factorization_monoid.factors UniqueFactorizationMonoid.factors

def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a
#align unique_factorization_monoid.normalized_factors UniqueFactorizationMonoid.normalizedFactors

def normalizationMonoid : NormalizationMonoid α :=
  normalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α → α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α → Associates α) := by
        ext x
        rw [Function.comp_apply, mkMonoidHom_apply,
          Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx, ← mkMonoidHom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ←
        associated_iff_eq]
      apply normalizedFactors_prod hx)
#align unique_factorization_monoid.normalization_monoid UniqueFactorizationMonoid.normalizationMonoid

def FactorSet.{u} (α : Type u) [CancelCommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })
#align associates.factor_set Associates.FactorSet

def FactorSet.prod : FactorSet α → Associates α
  | none => 0
  | some s => (s.map (↑)).prod
#align associates.factor_set.prod Associates.FactorSet.prod

def bcount [DecidableEq (Associates α)] (p : { a : Associates α // Irreducible a }) :
    FactorSet α → ℕ
  | none => 0
  | some s => s.count p
#align associates.bcount Associates.bcount

def count [DecidableEq (Associates α)] (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0
#align associates.count Associates.count

def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l
#align associates.bfactor_set_mem Associates.BfactorSetMem

def FactorSetMem (p : Associates α) (s : FactorSet α) : Prop :=
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False
#align associates.factor_set_mem Associates.FactorSetMem

def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, (irreducible_mk _).2 ha⟩) irreducible_of_factor
#align associates.factors' Associates.factors'

def factors (a : Associates α) : FactorSet α := by
  classical refine' if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => some <| factors' x) _ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
  exact fun ha hb _ => heq_of_eq <| congr_arg some <| factors'_cong hab
#align associates.factors Associates.factors

def UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] : GCDMonoid α where
  gcd a b := Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk, (Associates.mk a ⊓ Associates.mk b).quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk, (Associates.mk a ⊓ Associates.mk b).quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk, (Associates.mk c ⊓ Associates.mk b).quot_out, congr_fun₂ dvd_eq_le, le_inf_iff,
      mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by
    have : Associates.mk (0 : α) = ⊤ := rfl
    dsimp
    rw [this, top_sup_eq, ← this, ← associated_zero_iff_eq_zero, ← mk_eq_mk_iff_associated, ←
      associated_iff_eq, Associates.quot_out]
  lcm_zero_right a := by
    have : Associates.mk (0 : α) = ⊤ := rfl
    dsimp
    rw [this, sup_top_eq, ← this, ← associated_zero_iff_eq_zero, ← mk_eq_mk_iff_associated, ←
      associated_iff_eq, Associates.quot_out]
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated, ← Associates.mk_mul_mk, ← associated_iff_eq, Associates.quot_out,
      Associates.quot_out, mul_comm, sup_mul_inf, Associates.mk_mul_mk]
#align unique_factorization_monoid.to_gcd_monoid UniqueFactorizationMonoid.toGCDMonoid

def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_left
    gcd_dvd_right := fun a b =>
      (out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff];
          exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
    gcd_mul_lcm := fun a b => by
      rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }
#align unique_factorization_monoid.to_normalized_gcd_monoid UniqueFactorizationMonoid.toNormalizedGCDMonoid

def fintypeSubtypeDvd {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Fintype Mˣ] (y : M) (hy : y ≠ 0) : Fintype { x // x ∣ y } := by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : NormalizationMonoid M := UniqueFactorizationMonoid.normalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `λ (u : Mˣ) (f ⊆ factors y) → u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine'
    Fintype.ofFinset
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => _
  simp only [exists_prop, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true_iff,
    Multiset.mem_toFinset, Multiset.mem_powerset, exists_eq_right, Multiset.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show (s.snd : M) * s.fst.prod ∣ y
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mul,
      ← (normalizedFactors_prod hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x ≠ 0 := by
      refine' mt (fun hx => _) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := normalizedFactors_prod hx
    refine' ⟨⟨normalizedFactors x, u⟩, _, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h
#align unique_factorization_monoid.fintype_subtype_dvd UniqueFactorizationMonoid.fintypeSubtypeDvd

def factorization (n : α) : α →₀ ℕ :=
  Multiset.toFinsupp (normalizedFactors n)
#align factorization factorization

structure on `FactorSet`.

-/


variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop where
  wellFounded_dvdNotUnit : WellFounded (@DvdNotUnit α _)
#align wf_dvd_monoid WfDvdMonoid

structure on a `UniqueFactorizationMonoid`. -/
protected noncomputable def normalizationMonoid : NormalizationMonoid α :=
  normalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α → α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α → Associates α) := by
        ext x
        rw [Function.comp_apply, mkMonoidHom_apply,
          Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx, ← mkMonoidHom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ←
        associated_iff_eq]
      apply normalizedFactors_prod hx)
#align unique_factorization_monoid.normalization_monoid UniqueFactorizationMonoid.normalizationMonoid