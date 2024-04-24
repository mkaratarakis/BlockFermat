def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }
#align subfield.to_add_subgroup Subfield.toAddSubgroup

def toSubmonoid (s : Subfield K) : Submonoid K :=
--   { s.toSubring.toSubmonoid with }
-- #align subfield.to_submonoid Subfield.toSubmonoid

def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }
#align subfield.copy Subfield.copy

def Subring.toSubfield (s : Subring K) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : Subfield K :=
  { s with inv_mem' := hinv }
#align subring.to_subfield Subring.toSubfield

def subtype (s : Subfield K) : s →+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }
#align subfield.subtype Subfield.subtype

def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv
#align subfield.top_equiv Subfield.topEquiv

def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ ∈ s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }
#align subfield.comap Subfield.comap

def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }
#align subfield.map Subfield.map

def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.field_range RingHom.fieldRange

def closure (s : Set K) : Subfield K := sInf {S | s ⊆ S}
#align subfield.closure Subfield.closure

def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align subfield.gi Subfield.gi

def rangeRestrictField (f : K →+* L) : K →+* f.fieldRange :=
  f.rangeSRestrict
#align ring_hom.range_restrict_field RingHom.rangeRestrictField

def eqLocusField (f g : K →+* L) : Subfield K where
  __ := (f : K →+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }
#align ring_hom.eq_locus_field RingHom.eqLocusField

def inclusion {S T : Subfield K} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align subfield.inclusion Subfield.inclusion

def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subfield_congr RingEquiv.subfieldCongr

def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ x ∈ Subring.closure s, ∃ y ∈ Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩

private theorem commClosure_eq_closure {s : Set K} : commClosure s = closure s :=
  le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ ↦ eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx ↦ ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)

theorem mem_closure_iff {s : Set K} {x} :
    x ∈ closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl
#align subfield.mem_closure_iff Subfield.mem_closure_iff

structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

structure -/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s :=
  Subtype.coe_injective.divisionRing ((↑) : s → K)
    (by rfl) (by rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _; rfl)
    (by intros _ _; rfl) (by intros _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
    (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
    (by intros _; rfl) (by intros _; rfl) (by intros _; rfl)

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a field inherits a field structure -/
instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s :=
  Subtype.coe_injective.field ((↑) : s → K)
    (by rfl) (by rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _; rfl)
    (by intros _ _; rfl) (by intros _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
    (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl) (by intros _ _; rfl)
    (by intros _; rfl) (by intros _; rfl) (by intros _; rfl)
#align subfield_class.to_field SubfieldClass.toField

structure Subfield (K : Type u) [DivisionRing K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier
#align subfield Subfield

structure -/
instance toField {K} [Field K] (s : Subfield K) : Field s :=
  Subtype.coe_injective.field ((↑) : s → K) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) fun _ => rfl
#align subfield.to_field Subfield.toField