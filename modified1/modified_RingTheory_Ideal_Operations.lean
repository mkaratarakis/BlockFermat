def _root_.Module.annihilator : Ideal R := LinearMap.ker (LinearMap.lsmul R M)

theorem _root_.Module.mem_annihilator {r} : r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  ⟨fun h ↦ (congr($h ·)), (LinearMap.ext ·)⟩

theorem _root_.LinearMap.annihilator_le_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f) :
    Module.annihilator R M' ≤ Module.annihilator R M := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢; exact fun m ↦ hf (by rw [map_smul, h, f.map_zero])

theorem _root_.LinearMap.annihilator_le_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : Module.annihilator R M ≤ Module.annihilator R M' := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul, h, f.map_zero]

theorem _root_.LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') :
    Module.annihilator R M = Module.annihilator R M' :=
  (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
abbrev annihilator (N : Submodule R M) : Ideal R :=
  Module.annihilator R N
#align submodule.annihilator Submodule.annihilator

def colon (N P : Submodule R M) : Ideal R :=
  annihilator (P.map N.mkQ)
#align submodule.colon Submodule.colon

def radical (I : Ideal R) : Ideal R where
  carrier := { r | ∃ n : ℕ, r ^ n ∈ I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun {x y} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
-- Porting note: Below gives weird errors without `by exact`
  smul_mem' {r s} := by exact fun ⟨n, h⟩ ↦ ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩
#align ideal.radical Ideal.radical

def IsRadical (I : Ideal R) : Prop :=
  I.radical ≤ I
#align ideal.is_radical Ideal.IsRadical

def map (I : Ideal R) : Ideal S :=
  span (f '' I)
#align ideal.map Ideal.map

def comap (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx
#align ideal.comap Ideal.comap

def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)
#align ideal.gi_map_comap Ideal.giMapComap

def relIsoOfSurjective : Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
    Subtype.eq <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩
#align ideal.rel_iso_of_surjective Ideal.relIsoOfSurjective

def orderEmbeddingOfSurjective : Ideal S ↪o Ideal R :=
  (relIsoOfSurjective f hf).toRelEmbedding.trans (Subtype.relEmbedding (fun x y => x ≤ y) _)
#align ideal.order_embedding_of_surjective Ideal.orderEmbeddingOfSurjective

def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := (relIsoOfSurjective f hf.right).left_inv
  right_inv J :=
    Subtype.ext_iff.1
      ((relIsoOfSurjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩)
  map_rel_iff' {_ _} := (relIsoOfSurjective f hf.right).map_rel_iff'
#align ideal.rel_iso_of_bijective Ideal.relIsoOfBijective

def mapHom : Ideal R →*₀ Ideal S where
  toFun := map f
  map_mul' I J := Ideal.map_mul f I J
  map_one' := by simp only [one_eq_top]; exact Ideal.map_top f
  map_zero' := Ideal.map_bot
#align ideal.map_hom Ideal.mapHom

def IsPrimary (I : Ideal R) : Prop :=
  I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I
#align ideal.is_primary Ideal.IsPrimary

def finsuppTotal : (ι →₀ I) →ₗ[R] M :=
  (Finsupp.total ι M R v).comp (Finsupp.mapRange.linearMap I.subtype)
#align ideal.finsupp_total Ideal.finsuppTotal

def basisSpanSingleton (b : Basis ι R S) {x : S} (hx : x ≠ 0) :
    Basis ι R (span ({x} : Set S)) :=
  b.map <|
    LinearEquiv.ofInjective (Algebra.lmul R S x) (LinearMap.mul_injective hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R
#align ideal.basis_span_singleton Ideal.basisSpanSingleton

def ker : Ideal R :=
  Ideal.comap f ⊥
#align ring_hom.ker RingHom.ker

def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) :
    B →+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_mul f]
      simp only [hf _] }
#align ring_hom.lift_of_right_inverse_aux RingHom.liftOfRightInverseAux

def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => (mem_ker _).mpr <| by simp [(mem_ker _).mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply, Subtype.coe_mk]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]
#align ring_hom.lift_of_right_inverse RingHom.liftOfRightInverse