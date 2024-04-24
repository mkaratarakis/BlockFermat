def map_ideal (I : Ideal R) : Ideal S where
  carrier := { z : S | ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 }
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    let Z : { x // x ∈ I } := ⟨(a'.2 : R) * (b'.1 : R) + (b'.2 : R) * (a'.1 : R),
      I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    use ⟨Z, a'.2 * b'.2⟩
    simp only [RingHom.map_add, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ←
      mul_assoc b, hb]
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    let Z : { x // x ∈ I } := ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    use ⟨Z, c'.2 * x'.2⟩
    simp only [← hx, ← hc, smul_eq_mul, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    ring
-- Porting note: removed #align declaration since it is a private def

def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := Ideal.comap (algebraMap R S) J
  inj' := Function.LeftInverse.injective (map_comap M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    exact fun hJ => (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ Ideal.map_mono hJ
    exact fun hJ => Ideal.comap_mono hJ
#align is_localization.order_embedding IsLocalization.orderEmbedding

def orderIsoOfPrime :
    { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.eq (map_comap M S J)
  right_inv I := Subtype.eq (comap_map_of_isPrime_disjoint M S I.1 I.2.1 I.2.2)
  map_rel_iff' := by
    rintro I I'
    constructor
    exact (fun h => show I.val ≤ I'.val from map_comap M S I.val ▸
      map_comap M S I'.val ▸ Ideal.map_mono h)
    exact fun h x hx => h hx
#align is_localization.order_iso_of_prime IsLocalization.orderIsoOfPrime