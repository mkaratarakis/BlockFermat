def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align subsemigroup.to_add_subsemigroup Subsemigroup.toAddSubsemigroup

def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align add_subsemigroup.to_subsemigroup AddSubsemigroup.toSubsemigroup

def comap (f : M →ₙ* N) (S : Subsemigroup N) :
    Subsemigroup M where
  carrier := f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact mul_mem ha hb
#align subsemigroup.comap Subsemigroup.comap

def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N where
  carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩
#align subsemigroup.map Subsemigroup.map

def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align subsemigroup.gci_map_comap Subsemigroup.gciMapComap

def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align subsemigroup.gi_map_comap Subsemigroup.giMapComap

def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl
#align mul_mem_class.mul_def MulMemClass.mul_def

def AddMemClass.add_def

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure."]
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S :=
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl
#align mul_mem_class.to_semigroup MulMemClass.toSemigroup

def subtype : S' →ₙ* M where
  toFun := Subtype.val; map_mul' := fun _ _ => rfl
#align mul_mem_class.subtype MulMemClass.subtype

def topEquiv : (⊤ : Subsemigroup M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align subsemigroup.top_equiv Subsemigroup.topEquiv

def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
#align subsemigroup.equiv_map_of_injective Subsemigroup.equivMapOfInjective

def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) where
  carrier := s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align subsemigroup.prod Subsemigroup.prod

def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }
#align subsemigroup.prod_equiv Subsemigroup.prodEquiv

def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm
#align mul_hom.srange MulHom.srange

def restrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)
#align mul_hom.restrict MulHom.restrict

def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) :
    M →ₙ* S where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.eq (map_mul f x y)
#align mul_hom.cod_restrict MulHom.codRestrict

def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩
#align mul_hom.srange_restrict MulHom.srangeRestrict

def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) :
    N'.comap f →ₙ* N' where
  toFun x := ⟨f x, x.prop⟩
  map_mul' x y := Subtype.eq <| map_mul (M := M) (N := N) f x y
#align mul_hom.subsemigroup_comap MulHom.subsemigroupComap

def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) :
    M' →ₙ* M'.map f where
  toFun x := ⟨f x, ⟨x, x.prop, rfl⟩⟩
  map_mul' x y := Subtype.eq <| map_mul (M := M) (N := N) f x y
#align mul_hom.subsemigroup_map MulHom.subsemigroupMap

def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2
#align subsemigroup.inclusion Subsemigroup.inclusion

def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.subsemigroup_congr MulEquiv.subsemigroupCongr

def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse MulEquiv.ofLeftInverse

def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map (e : M →ₙ* N) :=
  { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M →ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }
#align mul_equiv.subsemigroup_map MulEquiv.subsemigroupMap

structure on a subsemigroup

* `Subsemigroup.toSemigroup`, `Subsemigroup.toCommSemigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups