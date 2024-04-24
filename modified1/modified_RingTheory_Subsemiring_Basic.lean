def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }
#align subsemiring_class.subtype SubsemiringClass.subtype

def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }
#align subsemiring.copy Subsemiring.copy

def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using sm.mul_mem
#align subsemiring.mk' Subsemiring.mk'

def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }
#align subsemiring.subtype Subsemiring.subtype

def topEquiv : (⊤ : Subsemiring R) ≃+* R where
  toFun r := r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add
#align subsemiring.top_equiv Subsemiring.topEquiv

def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with carrier := f ⁻¹' s }
#align subsemiring.comap Subsemiring.comap

def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }
#align subsemiring.map Subsemiring.map

def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }
#align subsemiring.equiv_map_of_injective Subsemiring.equivMapOfInjective

def rangeS : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.srange RingHom.rangeS

def center : Subsemiring R :=
  { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center R }
#align subsemiring.center Subsemiring.center

def centralizer {R} [Semiring R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer _
    add_mem' := Set.add_mem_centralizer }
#align subsemiring.centralizer Subsemiring.centralizer

def closure (s : Set R) : Subsemiring R :=
  sInf { S | s ⊆ S }
#align subsemiring.closure Subsemiring.closure

def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }
#align submonoid.subsemiring_closure Submonoid.subsemiringClosure

def gi : GaloisInsertion (@closure R _) (↑)
    where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align subsemiring.gi Subsemiring.gi

def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }
#align subsemiring.prod Subsemiring.prod

def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align subsemiring.prod_equiv Subsemiring.prodEquiv

def domRestrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s
#align ring_hom.dom_restrict RingHom.domRestrict

def codRestrict (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }
#align ring_hom.cod_restrict RingHom.codRestrict

def restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) : s' →+* s :=
  (f.domRestrict s').codRestrict s fun x => h x x.2
#align ring_hom.restrict RingHom.restrict

def rangeSRestrict (f : R →+* S) : R →+* f.rangeS :=
  f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self
#align ring_hom.srange_restrict RingHom.rangeSRestrict

def eqLocusS (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocusM g with carrier := { x | f x = g x } }
#align ring_hom.eq_slocus RingHom.eqLocusS

def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align subsemiring.inclusion Subsemiring.inclusion

def subsemiringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subsemiring_congr RingEquiv.subsemiringCongr

def ofLeftInverseS {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.rangeS :=
  { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align ring_equiv.sof_left_inverse RingEquiv.ofLeftInverseS

def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map e.toRingHom :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }
#align ring_equiv.subsemiring_map RingEquiv.subsemiringMap

def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl
#align subsemiring.smul_def Subsemiring.smul_def

def closureCommSemiringOfComm {s : Set R'} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (closure s) :=
  { (closure s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [Subsemiring.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [zero_mul, mul_zero])
          (fun x => by simp only [zero_mul, mul_zero]) (fun x => by simp only [one_mul, mul_one])
          (fun x => by simp only [one_mul, mul_one])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]) fun x y z h₁ h₂ =>
          by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }
#align subsemiring.closure_comm_semiring_of_comm Subsemiring.closureCommSemiringOfComm

structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s :=
  Subtype.coe_injective.nonAssocSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_non_assoc_semiring SubsemiringClass.toNonAssocSemiring

structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R
#align subsemiring Subsemiring

structure -/
instance toNonAssocSemiring : NonAssocSemiring s :=
  -- Porting note: this used to be a specialized instance which needed to be expensively unified.
  SubsemiringClass.toNonAssocSemiring _
#align subsemiring.to_non_assoc_semiring Subsemiring.toNonAssocSemiring