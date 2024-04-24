def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb}
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align submonoid.to_add_submonoid Submonoid.toAddSubmonoid

def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb}
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
#align add_submonoid.to_submonoid AddSubmonoid.toSubmonoid

def comap (f : F) (S : Submonoid N) :
    Submonoid M where
  carrier := f ⁻¹' S
  one_mem' := show f 1 ∈ S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact S.mul_mem ha hb
#align submonoid.comap Submonoid.comap

def map (f : F) (S : Submonoid M) :
    Submonoid N where
  carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩;
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩
#align submonoid.map Submonoid.map

def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align submonoid.gci_map_comap Submonoid.gciMapComap

def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align submonoid.gi_map_comap Submonoid.giMapComap

def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl
#align one_mem_class.one_def OneMemClass.one_def

def ZeroMemClass.zero_def

end OneMemClass

variable {A : Type*} [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

/-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/
instance AddSubmonoidClass.nSMul {M} [AddMonoid M] {A : Type*} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul ℕ S :=
  ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩
#align add_submonoid_class.has_nsmul AddSubmonoidClass.nSMul

def subtype : S' →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp
#align submonoid_class.subtype SubmonoidClass.subtype

def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl
#align submonoid.mul_def Submonoid.mul_def

def AddSubmonoid.add_def

@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl
#align submonoid.one_def Submonoid.one_def

def AddSubmonoid.zero_def

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure."]
instance toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  Subtype.coe_injective.mulOneClass (↑) rfl fun _ _ => rfl
#align submonoid.to_mul_one_class Submonoid.toMulOneClass

def subtype : S →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp
#align submonoid.subtype Submonoid.subtype

def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align submonoid.top_equiv Submonoid.topEquiv

def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }
#align submonoid.equiv_map_of_injective Submonoid.equivMapOfInjective

def prod (s : Submonoid M) (t : Submonoid N) :
    Submonoid (M × N) where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align submonoid.prod Submonoid.prod

def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }
#align submonoid.prod_equiv Submonoid.prodEquiv

def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M :=
  { carrier  := s,
    one_mem' := hs.symm ▸ S.one_mem',
    mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[to_additive "The range of an `AddMonoidHom` is an `AddSubmonoid`."]
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
#align monoid_hom.mrange MonoidHom.mrange

def restrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
    (s : S) : s →* N :=
  f.comp (SubmonoidClass.subtype _)
#align monoid_hom.restrict MonoidHom.restrict

def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.cod_restrict MonoidHom.codRestrict

def mrangeRestrict {N} [MulOneClass N] (f : M →* N) : M →* (mrange f) :=
  (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict MonoidHom.mrangeRestrict

def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f
#align monoid_hom.mker MonoidHom.mker

def submonoidComap (f : M →* N) (N' : Submonoid N) :
    N'.comap f →* N' where
  toFun x := ⟨f x, x.2⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.submonoid_comap MonoidHom.submonoidComap

def submonoidMap (f : M →* N) (M' : Submonoid M) : M' →* M'.map f where
  toFun x := ⟨f x, ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.eq <| f.map_one
  map_mul' x y := Subtype.eq <| f.map_mul x y
#align monoid_hom.submonoid_map MonoidHom.submonoidMap

def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align submonoid.inclusion Submonoid.inclusion

def submonoidCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.submonoid_congr MulEquiv.submonoidCongr

def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ f.mrange.subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse' MulEquiv.ofLeftInverse'

def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e.toMonoidHom :=
  { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }
#align mul_equiv.submonoid_map MulEquiv.submonoidMap

def (g : S) (a : α) : g • a = (g : M') • a := rfl
#align submonoid.smul_def Submonoid.smul_def

structure on a submonoid

* `Submonoid.toMonoid`, `Submonoid.toCommMonoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids