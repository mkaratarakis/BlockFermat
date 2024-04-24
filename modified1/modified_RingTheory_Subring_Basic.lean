def subtype (s : S) : s →+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }
#align subring_class.subtype SubringClass.subtype

def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }
#align subring.copy Subring.copy

def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }
#align subring.mk' Subring.mk'

def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R where
  toSubsemiring := s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h
#align subsemiring.to_subring Subsemiring.toSubring

def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }
#align subring.subtype Subring.subtype

def topEquiv : (⊤ : Subring R) ≃+* R :=
  Subsemiring.topEquiv
#align subring.top_equiv Subring.topEquiv

def comap {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }
#align subring.comap Subring.comap

def map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }
#align subring.map Subring.map

def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }
#align subring.equiv_map_of_injective Subring.equivMapOfInjective

def range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.range RingHom.range

def center : Subring R :=
  { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }
#align subring.center Subring.center

def centralizer (s : Set R) : Subring R :=
  { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }
#align subring.centralizer Subring.centralizer

def closure (s : Set R) : Subring R :=
  sInf { S | s ⊆ S }
#align subring.closure Subring.closure

def closureCommRingOfComm {s : Set R} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (closure s) :=
  { (closure s).toRing with
    mul_comm := fun x y => by
      ext
      simp only [Subring.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [mul_zero, zero_mul])
          (fun x => by simp only [mul_zero, zero_mul]) (fun x => by simp only [mul_one, one_mul])
          (fun x => by simp only [mul_one, one_mul])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }
#align subring.closure_comm_ring_of_comm Subring.closureCommRingOfComm

def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl
#align subring.gi Subring.gi

def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }
#align subring.prod Subring.prod

def prodEquiv (s : Subring R) (t : Subring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }
#align subring.prod_equiv Subring.prodEquiv

def rangeRestrict (f : R →+* S) : R →+* f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩
#align ring_hom.range_restrict RingHom.rangeRestrict

def eqLocus (f g : R →+* S) : Subring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocus g with carrier := { x | f x = g x } }
#align ring_hom.eq_locus RingHom.eqLocus

def inclusion {S T : Subring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align subring.inclusion Subring.inclusion

def subringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subring_congr RingEquiv.subringCongr

def ofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align ring_equiv.of_left_inverse RingEquiv.ofLeftInverse

def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring
#align ring_equiv.subring_map RingEquiv.subringMap

def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl
#align subring.smul_def Subring.smul_def

structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

structure -/
instance (priority := 75) toRing : Ring s :=
  Subtype.coe_injective.ring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ring SubringClass.toRing

structure Subring (R : Type u) [Ring R] extends Subsemiring R, AddSubgroup R
#align subring Subring

structure -/
instance toRing : Ring s := SubringClass.toRing s
#align subring.to_ring Subring.toRing