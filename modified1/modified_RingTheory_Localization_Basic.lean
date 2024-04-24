def toLocalizationWithZeroMap : Submonoid.LocalizationWithZeroMap M S where
  __ := algebraMap R S
  toFun := algebraMap R S
  map_units' := IsLocalization.map_units _
  surj' := IsLocalization.surj _
  exists_of_eq _ _ := IsLocalization.exists_of_eq
#align is_localization.to_localization_with_zero_map IsLocalization.toLocalizationWithZeroMap

def sec (z : S) : R × M :=
  Classical.choose <| IsLocalization.surj _ z
#align is_localization.sec IsLocalization.sec

def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y
#align is_localization.mk' IsLocalization.mk'

def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
  Fintype.ofSurjective (Function.uncurry <| IsLocalization.mk' S) fun a =>
    Prod.exists'.mpr <| IsLocalization.mk'_surjective M a
#align is_localization.fintype' IsLocalization.fintype'

def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩
#align is_localization.unique_of_zero_mem IsLocalization.uniqueOfZeroMem

def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  { Submonoid.LocalizationWithZeroMap.lift (toLocalizationWithZeroMap M S)
      g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      erw [(toLocalizationMap M S).lift_spec, mul_add, mul_comm, eq_comm, lift_spec_mul_add,
        add_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, lift_spec_mul_add]
      simp_rw [← mul_assoc]
      show g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      simp_rw [← map_mul g, ← map_add g]
      apply eq_of_eq (S := S) hg
      simp only [sec_spec', toLocalizationMap_sec, map_add, map_mul]
      ring }
#align is_localization.lift IsLocalization.lift

def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩
#align is_localization.map IsLocalization.map

def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id, ← H, Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp
    right_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp }
#align is_localization.ring_equiv_of_ring_equiv IsLocalization.ringEquivOfRingEquiv

def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }
#align is_localization.alg_equiv IsLocalization.algEquiv

def atUnits (H : M ≤ IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine' AlgEquiv.ofBijective (Algebra.ofId R S) ⟨_, _⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [RingHom.map_mul, ← eq, ← hu, mul_assoc, ← RingHom.map_mul]
    simp
#align is_localization.at_units IsLocalization.atUnits

def add (z w : Localization M) : Localization M :=
  Localization.liftOn₂ z w (fun a b c d => mk ((b : R) * c + d * a) (b * d))
    fun {a a' b b' c c' d d'} h1 h2 =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h1 h2 ⊢
        cases' h1 with t₅ ht₅
        cases' h2 with t₆ ht₆
        use t₅ * t₆
        dsimp only
        calc
          ↑t₅ * ↑t₆ * (↑b' * ↑d' * ((b : R) * c + d * a)) =
              t₆ * (d' * c) * (t₅ * (b' * b)) + t₅ * (b' * a) * (t₆ * (d' * d)) :=
            by ring
          _ = t₅ * t₆ * (b * d * (b' * c' + d' * a')) := by rw [ht₆, ht₅]; ring
          )
#align localization.add Localization.add

def mkAddMonoidHom (b : M) : R →+ Localization M where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm
#align localization.mk_add_monoid_hom Localization.mkAddMonoidHom

def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _
#align localization.alg_equiv Localization.algEquiv

def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique
#align is_localization.unique IsLocalization.unique

def neg (z : Localization M) : Localization M :=
  Localization.liftOn z (fun a b => mk (-a) b) fun {a b c d} h =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h ⊢
        cases' h with t ht
        use t
        rw [mul_neg, mul_neg, ht]
        ring_nf)
#align localization.neg Localization.neg

def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
#align localization_algebra localizationAlgebra

structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags

structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
#align localization_algebra localizationAlgebra