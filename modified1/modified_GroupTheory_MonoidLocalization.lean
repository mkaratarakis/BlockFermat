def r (S : Submonoid M) : Con (M × S) :=
  sInf { c | ∀ y : S, c 1 (y, y) }
#align localization.r Localization.r

def r' : Con (M × S) := by
  -- note we multiply by `c` on the left so that we can later generalize to `•`
  refine
    { r := fun a b : M × S ↦ ∃ c : S, ↑c * (↑b.2 * a.1) = c * (a.2 * b.1)
      iseqv := ⟨fun a ↦ ⟨1, rfl⟩, fun ⟨c, hc⟩ ↦ ⟨c, hc.symm⟩, ?_⟩
      mul' := ?_ }
  · rintro a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁ * b.2
    simp only [Submonoid.coe_mul]
    calc
      (t₂ * t₁ * b.2 : M) * (c.2 * a.1) = t₂ * c.2 * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = t₁ * a.2 * (t₂ * (c.2 * b.1)) := by rw [ht₁]; ac_rfl
      _ = t₂ * t₁ * b.2 * (a.2 * c.1) := by rw [ht₂]; ac_rfl
  · rintro a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁
    calc
      (t₂ * t₁ : M) * (b.2 * d.2 * (a.1 * c.1)) = t₂ * (d.2 * c.1) * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = (t₂ * t₁ : M) * (a.2 * c.2 * (b.1 * d.1)) := by rw [ht₁, ht₂]; ac_rfl
#align localization.r' Localization.r'

def Localization := (Localization.r S).Quotient
#align localization Localization

def mul : Localization S → Localization S → Localization S :=
  (r S).commMonoid.mul
#align localization.mul Localization.mul

def one : Localization S := (r S).commMonoid.one
#align localization.one Localization.one

def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less.
-/
@[to_additive "Multiplication with a natural in an `AddLocalization` is defined as
`n • ⟨a, b⟩ = ⟨n • a, n • b⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less."]
protected irreducible_def npow : ℕ → Localization S → Localization S := (r S).commMonoid.npow
#align localization.npow Localization.npow

def mk (x : M) (y : S) : Localization S := (r S).mk' (x, y)
#align localization.mk Localization.mk

def rec {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b))
    (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)),
      (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d) (x) : p x :=
  Quot.rec (fun y ↦ Eq.ndrec (f y.1 y.2) (by rfl)) (fun y z h ↦ by cases y; cases z; exact H h) x
#align localization.rec Localization.rec

def recOnSubsingleton₂ {r : Localization S → Localization S → Sort u}
    [h : ∀ (a c : M) (b d : S), Subsingleton (r (mk a b) (mk c d))] (x y : Localization S)
    (f : ∀ (a c : M) (b d : S), r (mk a b) (mk c d)) : r x y :=
  @Quotient.recOnSubsingleton₂' _ _ _ _ r (Prod.rec fun _ _ => Prod.rec fun _ _ => h _ _ _ _) x y
    (Prod.rec fun _ _ => Prod.rec fun _ _ => f _ _ _ _)
#align localization.rec_on_subsingleton₂ Localization.recOnSubsingleton₂

def liftOn {p : Sort u} (x : Localization S) (f : M → S → p)
    (H : ∀ {a c : M} {b d : S}, r S (a, b) (c, d) → f a b = f c d) : p :=
  rec f (fun h ↦ (by simpa only [eq_rec_constant] using H h)) x
#align localization.lift_on Localization.liftOn

def liftOn₂ {p : Sort u} (x y : Localization S) (f : M → S → M → S → p)
    (H : ∀ {a a' b b' c c' d d'}, r S (a, b) (a', b') → r S (c, d) (c', d') →
      f a b c d = f a' b' c' d') : p :=
  liftOn x (fun a b ↦ liftOn y (f a b) fun hy ↦ H ((r S).refl _) hy) fun hx ↦
    induction_on y fun ⟨_, _⟩ ↦ H hx ((r S).refl _)
#align localization.lift_on₂ Localization.liftOn₂

def smul [SMul R M] [IsScalarTower R M M] (c : R) (z : Localization S) :
  Localization S :=
    Localization.liftOn z (fun a b ↦ mk (c • a) b)
      (fun {a a' b b'} h ↦ mk_eq_mk_iff.2 (by
        let ⟨b, hb⟩ := b
        let ⟨b', hb'⟩ := b'
        rw [r_eq_r'] at h ⊢
        let ⟨t, ht⟩ := h
        use t
        dsimp only [Subtype.coe_mk] at ht ⊢
-- TODO: this definition should take `SMulCommClass R M M` instead of `IsScalarTower R M M` if
-- we ever want to generalize to the non-commutative case.
        haveI : SMulCommClass R M M :=
          ⟨fun r m₁ m₂ ↦ by simp_rw [smul_eq_mul, mul_comm m₁, smul_mul_assoc]⟩
        simp only [mul_smul_comm, ht]))
#align localization.smul Localization.smul

def toLocalizationMap (f : M →* N) (H1 : ∀ y : S, IsUnit (f y))
    (H2 : ∀ z, ∃ x : M × S, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y → ∃ c : S, ↑c * x = ↑c * y) :
    Submonoid.LocalizationMap S N :=
  { f with
    map_units' := H1
    surj' := H2
    exists_of_eq := H3 }
#align monoid_hom.to_localization_map MonoidHom.toLocalizationMap

def sec (f : LocalizationMap S N) (z : N) : M × S := Classical.choose <| f.surj z
#align submonoid.localization_map.sec Submonoid.LocalizationMap.sec

def mk' (f : LocalizationMap S N) (x : M) (y : S) : N :=
  f.toMap x * ↑(IsUnit.liftRight (f.toMap.restrict S) f.map_units y)⁻¹
#align submonoid.localization_map.mk' Submonoid.LocalizationMap.mk'

def lift : N →* P where
  toFun z := g (f.sec z).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    dsimp only
    rw [mul_inv_left hg, ← mul_assoc, ← mul_assoc, mul_inv_right hg, mul_comm _ (g (f.sec y).1), ←
      mul_assoc, ← mul_assoc, mul_inv_right hg]
    repeat' rw [← g.map_mul]
    exact f.eq_of_eq hg (by simp_rw [f.toMap.map_mul, sec_spec']; ac_rfl)
#align submonoid.localization_map.lift Submonoid.LocalizationMap.lift

def map : N →* Q :=
  @lift _ _ _ _ _ _ _ f (k.toMap.comp g) fun y ↦ k.map_units ⟨g y, hy y⟩
#align submonoid.localization_map.map Submonoid.LocalizationMap.map

def AwayMap (N' : Type*) [CommMonoid N'] := LocalizationMap (powers x) N'
#align submonoid.localization_map.away_map Submonoid.LocalizationMap.AwayMap

def AwayMap.invSelf : N := F.mk' 1 ⟨x, mem_powers _⟩
#align submonoid.localization_map.away_map.inv_self Submonoid.LocalizationMap.AwayMap.invSelf

def AwayMap.lift (hg : IsUnit (g x)) : N →* P :=
  Submonoid.LocalizationMap.lift F fun y ↦
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.pow n hg
#align submonoid.localization_map.away_map.lift Submonoid.LocalizationMap.AwayMap.lift

def awayToAwayRight (y : M) (G : AwayMap (x * y) P) : N →* P :=
  F.lift x <|
    show IsUnit (G.toMap x) from
      isUnit_of_mul_eq_one (G.toMap x) (G.mk' y ⟨x * y, mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]
#align submonoid.localization_map.away_to_away_right Submonoid.LocalizationMap.awayToAwayRight

def AwayMap.negSelf : B :=
  F.mk' 0 ⟨x, mem_multiples _⟩
#align add_submonoid.localization_map.away_map.neg_self AddSubmonoid.LocalizationMap.AwayMap.negSelf

def AwayMap.lift (hg : IsAddUnit (g x)) : B →+ C :=
  AddSubmonoid.LocalizationMap.lift F fun y ↦
    show IsAddUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]
      dsimp
      rw [g.map_nsmul]
      exact IsAddUnit.map (nsmulAddMonoidHom n : C →+ C) hg
#align add_submonoid.localization_map.away_map.lift AddSubmonoid.LocalizationMap.AwayMap.lift

def awayToAwayRight (y : A) (G : AwayMap (x + y) C) : B →+ C :=
  F.lift x <|
    show IsAddUnit (G.toMap x) from
      isAddUnit_of_add_eq_zero (G.toMap x) (G.mk' y ⟨x + y, mem_multiples _⟩) <| by
        rw [add_mk'_eq_mk'_of_add, mk'_self]
#align add_submonoid.localization_map.away_to_away_right AddSubmonoid.LocalizationMap.awayToAwayRight

def mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P :=
{ toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := MonoidHom.map_mul _ }
#align submonoid.localization_map.mul_equiv_of_localizations Submonoid.LocalizationMap.mulEquivOfLocalizations

def ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P :=
  (k.toMonoidHom.comp f.toMap).toLocalizationMap (fun y ↦ isUnit_comp f k.toMonoidHom y)
    (fun v ↦
      let ⟨z, hz⟩ := k.toEquiv.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k _ = k _ by rw [← hx, k.map_mul, ← hz]; rfl⟩)
    fun x y ↦ (k.apply_eq_iff_eq.trans f.eq_iff_exists).1
#align submonoid.localization_map.of_mul_equiv_of_localizations Submonoid.LocalizationMap.ofMulEquivOfLocalizations

def ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationMap T N :=
  let H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMap.comp k.toMonoidHom).toLocalizationMap
    (fun y ↦
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z ↦
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.toEquiv.surjective x.1
      let ⟨w, hw⟩ := k.toEquiv.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w ∈ S from hw.symm ▸ x.2.2⟩),
        show z * f.toMap (k.toEquiv w) = f.toMap (k.toEquiv v) by erw [hv, hw, hx]⟩)
    fun x y ↦
    show f.toMap _ = f.toMap _ → _ by
      erw [f.eq_iff_exists]
      exact
        fun ⟨c, hc⟩ ↦
          let ⟨d, hd⟩ := k.toEquiv.surjective c
          ⟨⟨d, H' ▸ show k d ∈ S from hd.symm ▸ c.2⟩, by
            erw [← hd, ← k.map_mul, ← k.map_mul] at hc; exact k.toEquiv.injective hc⟩
#align submonoid.localization_map.of_mul_equiv_of_dom Submonoid.LocalizationMap.ofMulEquivOfDom

def mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) : N ≃* Q :=
  f.mulEquivOfLocalizations <| k.ofMulEquivOfDom H
#align submonoid.localization_map.mul_equiv_of_mul_equiv Submonoid.LocalizationMap.mulEquivOfMulEquiv

def monoidOf : Submonoid.LocalizationMap S (Localization S) :=
  { (r S).mk'.comp <| MonoidHom.inl M
        S with
    toFun := fun x ↦ mk x 1
    map_one' := mk_one
    map_mul' := fun x y ↦ by dsimp only; rw [mk_mul, mul_one]
    map_units' := fun y ↦
      isUnit_iff_exists_inv.2 ⟨mk 1 y, by dsimp only; rw [mk_mul, mul_one, one_mul, mk_self]⟩
    surj' := fun z ↦ induction_on z fun x ↦
      ⟨x, by dsimp only; rw [mk_mul, mul_comm x.fst, ← mk_mul, mk_self, one_mul]⟩
    exists_of_eq := fun x y ↦ Iff.mp <|
      mk_eq_mk_iff.trans <|
        r_iff_exists.trans <|
          show (∃ c : S, ↑c * (1 * x) = c * (1 * y)) ↔ _ by rw [one_mul, one_mul] }
#align localization.monoid_of Localization.monoidOf

def mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoidOf S).mulEquivOfLocalizations f
#align localization.mul_equiv_of_quotient Localization.mulEquivOfQuotient

def Away :=
  Localization (Submonoid.powers x)
#align localization.away Localization.Away

def Away.invSelf : Away x :=
  mk 1 ⟨x, Submonoid.mem_powers _⟩
#align localization.away.inv_self Localization.Away.invSelf

def Away.monoidOf : Submonoid.LocalizationMap.AwayMap x (Away x) :=
  Localization.monoidOf (Submonoid.powers x)
#align localization.away.monoid_of Localization.Away.monoidOf

def Away.mulEquivOfQuotient (f : Submonoid.LocalizationMap.AwayMap x N) :
    Away x ≃* N :=
  Localization.mulEquivOfQuotient f
#align localization.away.mul_equiv_of_quotient Localization.Away.mulEquivOfQuotient

def LocalizationWithZeroMap.toMonoidWithZeroHom (f : LocalizationWithZeroMap S N) : M →*₀ N :=
  { f with }
#align submonoid.localization_with_zero_map.to_monoid_with_zero_hom Submonoid.LocalizationWithZeroMap.toMonoidWithZeroHom

def zero : Localization S :=
  mk 0 1
#align localization.zero Localization.zero

def S).symm

instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
#align localization.mk_zero Localization.mk_zero

def lift (f : LocalizationWithZeroMap S N) (g : M →*₀ P)
    (hg : ∀ y : S, IsUnit (g y)) : N →*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f.toLocalizationMap g.toMonoidHom hg with
    map_zero' := by
      erw [LocalizationMap.lift_spec f.toLocalizationMap hg 0 0]
      rw [mul_zero, ← map_zero g, ← g.toMonoidHom_coe]
      refine f.toLocalizationMap.eq_of_eq hg ?_
      rw [LocalizationMap.sec_zero_fst]
      exact f.toMonoidWithZeroHom.map_zero.symm }
#align submonoid.localization_with_zero_map.lift Submonoid.LocalizationWithZeroMap.lift

def mkOrderEmbedding (b : s) : α ↪o Localization s where
  toFun a := mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [-mk_eq_monoidOf_mk', mk_le_mk]
#align localization.mk_order_embedding Localization.mkOrderEmbedding

structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To apply a localization map `f` as a function, we use `f.toMap`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_monoidOf_mk'` and associated
lemmas. These show the quotient map `mk : M → S → Localization S` equals the
surjection `LocalizationMap.mk'` induced by the map
`Localization.monoidOf : Submonoid.LocalizationMap S (Localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoidOf_mk'` hence gives you access to the results in the rest of the file, which are about
the `LocalizationMap.mk'` induced by any localization map.

## TODO

structure LocalizationMap extends AddMonoidHom M N where
  map_add_units' : ∀ y : S, IsAddUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z + toFun x.2 = toFun x.1
  exists_of_eq : ∀ x y, toFun x = toFun y → ∃ c : S, ↑c + x = ↑c + y
#align add_submonoid.localization_map AddSubmonoid.LocalizationMap

structure LocalizationMap extends MonoidHom M N where
  map_units' : ∀ y : S, IsUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z * toFun x.2 = toFun x.1
  exists_of_eq : ∀ x y, toFun x = toFun y → ∃ c : S, ↑c * x = c * y
#align submonoid.localization_map Submonoid.LocalizationMap

structure LocalizationWithZeroMap extends LocalizationMap S N where
  map_zero' : toFun 0 = 0
#align submonoid.localization_with_zero_map Submonoid.LocalizationWithZeroMap