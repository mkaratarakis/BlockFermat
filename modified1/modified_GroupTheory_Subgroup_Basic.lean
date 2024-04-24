def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' := fun _ _ => rfl
#align subgroup_class.subtype SubgroupClass.subtype

def inclusion {H K : S} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.prop⟩) fun _ _=> rfl
#align subgroup_class.inclusion SubgroupClass.inclusion

def Subgroup.toAddSubgroup : Subgroup G ≃o AddSubgroup (Additive G) where
  toFun S := { Submonoid.toAddSubmonoid S.toSubmonoid with neg_mem' := S.inv_mem' }
  invFun S := { AddSubmonoid.toSubmonoid S.toAddSubmonoid with inv_mem' := S.neg_mem' }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align subgroup.to_add_subgroup Subgroup.toAddSubgroup

def AddSubgroup.toSubgroup : AddSubgroup A ≃o Subgroup (Multiplicative A) where
  toFun S := { AddSubmonoid.toSubmonoid S.toAddSubmonoid with inv_mem' := S.neg_mem' }
  invFun S := { Submonoid.toAddSubmonoid S.toSubmonoid with neg_mem' := S.inv_mem' }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align add_subgroup.to_subgroup AddSubgroup.toSubgroup

def copy (K : Subgroup G) (s : Set G) (hs : s = K) : Subgroup G where
  carrier := s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx -- Porting note: `▸` didn't work here
#align subgroup.copy Subgroup.copy

def ofDiv (s : Set G) (hsn : s.Nonempty) (hs : ∀ᵉ (x ∈ s) (y ∈ s), x * y⁻¹ ∈ s) :
    Subgroup G :=
  have one_mem : (1 : G) ∈ s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : ∀ x, x ∈ s → x⁻¹ ∈ s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _ (inv_mem _ hy) }
#align subgroup.of_div Subgroup.ofDiv

def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' _ _ := rfl
#align subgroup.subtype Subgroup.subtype

def inclusion {H K : Subgroup G} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl
#align subgroup.inclusion Subgroup.inclusion

def topEquiv : (⊤ : Subgroup G) ≃* G :=
  Submonoid.topEquiv
#align subgroup.top_equiv Subgroup.topEquiv

def closure (k : Set G) : Subgroup G :=
  sInf { K | k ⊆ K }
#align subgroup.closure Subgroup.closure

def closureCommGroupOfComm {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    CommGroup (closure k) :=
  { (closure k).toGroup with
    mul_comm := fun x y => by
      ext
      simp only [Subgroup.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [mul_one, one_mul])
          (fun x => by simp only [mul_one, one_mul])
          (fun x y z h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc])
          (fun x y z h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc])
          (fun x y h => by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_self, mul_one])
          fun x y h => by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, h, ← mul_assoc, inv_mul_self, one_mul] }
#align subgroup.closure_comm_group_of_comm Subgroup.closureCommGroupOfComm

def gi : GaloisInsertion (@closure G _) (↑)
    where
  choice s _ := closure s
  gc s t := @closure_le _ _ t s
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl
#align subgroup.gi Subgroup.gi

def comap {N : Type*} [Group N] (f : G →* N) (H : Subgroup N) : Subgroup G :=
  { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ ∈ H by rw [f.map_inv]; exact H.inv_mem ha }
#align subgroup.comap Subgroup.comap

def map (f : G →* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }
#align subgroup.map Subgroup.map

def subgroupOf (H K : Subgroup G) : Subgroup K :=
  H.comap K.subtype
#align subgroup.subgroup_of Subgroup.subgroupOf

def subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  left_inv _g := Subtype.ext (Subtype.ext rfl)
  right_inv _g := Subtype.ext rfl
  map_mul' _g _h := rfl
#align subgroup.subgroup_of_equiv_of_le Subgroup.subgroupOfEquivOfLe

def prod (H : Subgroup G) (K : Subgroup N) : Subgroup (G × N) :=
  { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }
#align subgroup.prod Subgroup.prod

def prodEquiv (H : Subgroup G) (K : Subgroup N) : H.prod K ≃* H × K :=
  { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }
#align subgroup.prod_equiv Subgroup.prodEquiv

def _root_.Submonoid.pi [∀ i, MulOneClass (f i)] (I : Set η) (s : ∀ i, Submonoid (f i)) :
    Submonoid (∀ i, f i) where
  carrier := I.pi fun i => (s i).carrier
  one_mem' i _ := (s i).one_mem
  mul_mem' hp hq i hI := (s i).mul_mem (hp i hI) (hq i hI)
#align submonoid.pi Submonoid.pi

def pi (I : Set η) (H : ∀ i, Subgroup (f i)) : Subgroup (∀ i, f i) :=
  { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }
#align subgroup.pi Subgroup.pi

def center : Subgroup G :=
  { Submonoid.center G with
    carrier := Set.center G
    inv_mem' := Set.inv_mem_center }
#align subgroup.center Subgroup.center

def centerUnitsEquivUnitsCenter (G₀ : Type*) [GroupWithZero G₀] :
    Subgroup.center (G₀ˣ) ≃* (Submonoid.center G₀)ˣ where
  toFun := MonoidHom.toHomUnits <|
    { toFun := fun u ↦ ⟨(u : G₀ˣ),
      (Submonoid.mem_center_iff.mpr (fun r ↦ by
          rcases eq_or_ne r 0 with (rfl | hr)
          · rw [mul_zero, zero_mul]
          exact congrArg Units.val <| (u.2.comm <| Units.mk0 r hr).symm))⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  invFun u := unitsCenterToCenterUnits G₀ u
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' := map_mul _

variable {G}

@[to_additive]
theorem mem_center_iff {z : G} : z ∈ center G ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align subgroup.mem_center_iff Subgroup.mem_center_iff

def _root_.Group.commGroupOfCenterEqTop (h : center G = ⊤) : CommGroup G :=
  { (_ : Group G) with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }
#align group.comm_group_of_center_eq_top Group.commGroupOfCenterEqTop

def normalizer : Subgroup G where
  carrier := { g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }
  one_mem' := by simp
  mul_mem' {a b} (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n := by
    rw [hb, ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_right_inv, mul_one]
#align subgroup.normalizer Subgroup.normalizer

def setNormalizer (S : Set G) : Subgroup G where
  carrier := { g : G | ∀ n, n ∈ S ↔ g * n * g⁻¹ ∈ S }
  one_mem' := by simp
  mul_mem' {a b} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) (hb : ∀ n, n ∈ S ↔ b * n * b⁻¹ ∈ S) n := by
    rw [hb, ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_right_inv, mul_one]
#align subgroup.set_normalizer Subgroup.setNormalizer

def _root_.NormalizerCondition :=
  ∀ H : Subgroup G, H < ⊤ → H < normalizer H
#align normalizer_condition NormalizerCondition

def centralizer (s : Set G) : Subgroup G :=
  { Submonoid.centralizer s with
    carrier := Set.centralizer s
    inv_mem' := Set.inv_mem_centralizer }
#align subgroup.centralizer Subgroup.centralizer

def conjugatesOfSet (s : Set G) : Set G :=
  ⋃ a ∈ s, conjugatesOf a
#align group.conjugates_of_set Group.conjugatesOfSet

def normalClosure (s : Set G) : Subgroup G :=
  closure (conjugatesOfSet s)
#align subgroup.normal_closure Subgroup.normalClosure

def normalCore (H : Subgroup G) : Subgroup G where
  carrier := { a : G | ∀ b : G, b * a * b⁻¹ ∈ H }
  one_mem' a := by rw [mul_one, mul_inv_self]; exact H.one_mem
  inv_mem' {a} h b := (congr_arg (· ∈ H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {a b} ha hb c := (congr_arg (· ∈ H) conj_mul).mp (H.mul_mem (ha c) (hb c))
#align subgroup.normal_core Subgroup.normalCore

def range (f : G →* N) : Subgroup N :=
  Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp [Set.ext_iff])
#align monoid_hom.range MonoidHom.range

def rangeRestrict (f : G →* N) : G →* f.range :=
  codRestrict f _ fun x => ⟨x, rfl⟩
#align monoid_hom.range_restrict MonoidHom.rangeRestrict

def ofLeftInverse {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f) : G ≃* f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      apply Subtype.ext
      rw [coe_rangeRestrict, Function.comp_apply, Subgroup.coeSubtype, Subtype.coe_mk, h] }
#align monoid_hom.of_left_inverse MonoidHom.ofLeftInverse

def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun x y h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩
#align monoid_hom.of_injective MonoidHom.ofInjective

def ker (f : G →* M) : Subgroup G :=
  { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_self, map_one] }
#align monoid_hom.ker MonoidHom.ker

def eqLocus (f g : G →* M) : Subgroup G :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }
#align monoid_hom.eq_locus MonoidHom.eqLocus

def equivMapOfInjective (H : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    H ≃* H.map f :=
  { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }
#align subgroup.equiv_map_of_injective Subgroup.equivMapOfInjective

def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃) (hg : f.ker ≤ g.ker) :
    G₂ →* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul, ← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
    apply hg
    rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one, f.map_mul]
    simp only [hf _]
#align monoid_hom.lift_of_right_inverse_aux MonoidHom.liftOfRightInverseAux

def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃)
    where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => (mem_ker _).mpr <| by simp [(mem_ker _).mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply, Subtype.coe_mk]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]
#align monoid_hom.lift_of_right_inverse MonoidHom.liftOfRightInverse

def subgroupComap (f : G →* G') (H' : Subgroup G') : H'.comap f →* H' :=
  f.submonoidComap H'.toSubmonoid
#align monoid_hom.subgroup_comap MonoidHom.subgroupComap

def subgroupMap (f : G →* G') (H : Subgroup G) : H →* H.map f :=
  f.submonoidMap H.toSubmonoid
#align monoid_hom.subgroup_map MonoidHom.subgroupMap

def subgroupCongr (h : H = K) : H ≃* K :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.subgroup_congr MulEquiv.subgroupCongr

def subgroupMap (e : G ≃* G') (H : Subgroup G) : H ≃* H.map (e : G →* G') :=
  MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid
#align mul_equiv.subgroup_map MulEquiv.subgroupMap

def {H₁ H₂ : Subgroup G} : Disjoint H₁ H₂ ↔ ∀ {x : G}, x ∈ H₁ → x ∈ H₂ → x = 1 :=
  disjoint_iff_inf_le.trans <| by simp only [Disjoint, SetLike.le_def, mem_inf, mem_bot, and_imp]
#align subgroup.disjoint_def Subgroup.disjoint_def

def AddSubgroup.disjoint_def

@[to_additive]
theorem disjoint_def' {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h _x _y hx hy hxy ↦ h hx <| hxy.symm ▸ hy, fun h _x hx hx' ↦ h hx hx' rfl⟩
#align subgroup.disjoint_def' Subgroup.disjoint_def'

structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier
#align subgroup Subgroup

structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x ∈ carrier → -x ∈ carrier
#align add_subgroup AddSubgroup

structure Normal : Prop where
  /-- `N` is closed under conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H
#align subgroup.normal Subgroup.Normal

structure Normal (H : AddSubgroup A) : Prop where
  /-- `N` is closed under additive conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : A, g + n + -g ∈ H
#align add_subgroup.normal AddSubgroup.Normal

structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
#align subgroup.characteristic Subgroup.Characteristic

structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H
#align add_subgroup.characteristic AddSubgroup.Characteristic

structure IsCommutative : Prop where
  /-- `*` is commutative on `H` -/
  is_comm : Std.Commutative (α := H) (· * ·)
#align subgroup.is_commutative Subgroup.IsCommutative

structure _root_.AddSubgroup.IsCommutative (H : AddSubgroup A) : Prop where
  /-- `+` is commutative on `H` -/
  is_comm : Std.Commutative (α := H) (· + ·)
#align add_subgroup.is_commutative AddSubgroup.IsCommutative