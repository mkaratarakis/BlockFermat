def DirectLimit : Type max v w :=
  DirectSum ι G ⧸
    (span R <|
      { a |
        ∃ (i j : _) (H : i ≤ j) (x : _),
          DirectSum.lof R ι G i x - DirectSum.lof R ι G j (f i j H x) = a })
#align module.direct_limit Module.DirectLimit

def of (i) : G i →ₗ[R] DirectLimit G f :=
  (mkQ _).comp <| DirectSum.lof R ι G i
#align module.direct_limit.of Module.DirectLimit.of

def lift : DirectLimit G f →ₗ[R] P :=
  liftQ _ (DirectSum.toModule R ι P g)
    (span_le.2 fun a ⟨i, j, hij, x, hx⟩ => by
      rw [← hx, SetLike.mem_coe, LinearMap.sub_mem_ker_iff, DirectSum.toModule_lof,
        DirectSum.toModule_lof, Hg])
#align module.direct_limit.lift Module.DirectLimit.lift

def map (g : (i : ι) → G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i) :
    DirectLimit G f →ₗ[R] DirectLimit G' f' :=
  lift _ _ _ _ (fun i ↦ of _ _ _ _ _ ∘ₗ g i) fun i j h g ↦ by
    cases isEmpty_or_nonempty ι
    · exact Subsingleton.elim _ _
    · have eq1 := LinearMap.congr_fun (hg i j h) g
      simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    {i : ι} (x : G i) :
    map g hg (of _ _ G f _ x) = of R ι G' f' i (g i x) :=
  lift_of _ _ _

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun i ↦ LinearMap.id) (fun _ _ _ ↦ rfl) = LinearMap.id (R := R) (M := DirectLimit G f) :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (fun _ ↦ Subsingleton.elim _ _) fun _ ↦
    x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →ₗ[R] G' i) (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (map g₂ hg₂ ∘ₗ map g₁ hg₁ :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') =
    (map (fun i ↦ g₂ i ∘ₗ g₁ i) fun i j h ↦ by
        rw [LinearMap.comp_assoc, hg₁ i, ← LinearMap.comp_assoc, hg₂ i, LinearMap.comp_assoc] :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (fun _ ↦ Subsingleton.elim _ _) fun _ ↦
    x.induction_on fun i g ↦ by simp

open LinearEquiv LinearMap in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ≅ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) :
    DirectLimit G f ≃ₗ[R] DirectLimit G' f' :=
  LinearEquiv.ofLinear (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ by
      rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
        refl_toLinearMap, comp_id])
    (by simp [map_comp]) (by simp [map_comp])

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    congr e he (of _ _ G f i g) = of _ _ G' f' i (e i g) :=
  map_apply_of _ he _

open LinearEquiv LinearMap in
lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G' i) :
    (congr e he).symm (of _ _ G' f' i g) = of _ _ G f i ((e i).symm g) :=
  map_apply_of _ (fun i j h ↦ by
    rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
      refl_toLinearMap, comp_id]) _

end functorial

section Totalize

open scoped Classical

variable (G f)

/-- `totalize G f i j` is a linear map from `G i` to `G j`, for *every* `i` and `j`.
If `i ≤ j`, then it is the map `f i j` that comes with the directed system `G`,
and otherwise it is the zero map. -/
noncomputable def totalize (i j) : G i →ₗ[R] G j :=
  if h : i ≤ j then f i j h else 0
#align module.direct_limit.totalize Module.DirectLimit.totalize

def DirectLimit (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℤ _ ι _ G _ _ (fun i j hij => (f i j hij).toIntLinearMap) _
#align add_comm_group.direct_limit AddCommGroup.DirectLimit

def of (i) : G i →+ DirectLimit G f :=
  (Module.DirectLimit.of ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap) i).toAddMonoidHom
#align add_comm_group.direct_limit.of AddCommGroup.DirectLimit.of

def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap)
    (fun i => (g i).toIntLinearMap) Hg).toAddMonoidHom
#align add_comm_group.direct_limit.lift AddCommGroup.DirectLimit.lift

def map (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G f →+ DirectLimit G' f' :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
    cases isEmpty_or_nonempty ι
    · exact Subsingleton.elim _ _
    · have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G f _ x) = of G' f' i (g i x) :=
  lift_of _ _ _ _ _

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun i ↦ AddMonoidHom.id _) (fun _ _ _ ↦ rfl) = AddMonoidHom.id (DirectLimit G f) :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (fun _ ↦ Subsingleton.elim _ _) fun _ ↦
    x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →+ G' i) (g₂ : (i : ι) → G' i →+ G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G f →+ DirectLimit G'' f'') =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [AddMonoidHom.comp_assoc, hg₁ i, ← AddMonoidHom.comp_assoc, hg₂ i,
        AddMonoidHom.comp_assoc] :
      DirectLimit G f →+ DirectLimit G'' f'') :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (fun _ ↦ Subsingleton.elim _ _) fun _ ↦
    x.induction_on fun i g ↦ by simp

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G f ≃+ DirectLimit G' f' :=
  AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1, of_f])
    (by rw [map_comp]; convert map_id <;> aesop)
    (by rw [map_comp]; convert map_id <;> aesop)

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G f i g) = of G' f' i (e i g) :=
  map_apply_of _ he _

lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g) := by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

end functorial

end DirectLimit

end AddCommGroup

namespace Ring

variable [∀ i, CommRing (G i)]

section

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

/-- The direct limit of a directed system is the rings glued together along the maps. -/
def DirectLimit : Type max v w :=
  FreeCommRing (Σi, G i) ⧸
    Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σi, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σi, G i) - 1 = a) ∨
            (∃ i x y, of (⟨i, x + y⟩ : Σi, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              ∃ i x y, of (⟨i, x * y⟩ : Σi, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
#align ring.direct_limit Ring.DirectLimit

def of (i) : G i →+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x => Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σi, G i))
      map_one' := Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inl ⟨i, rfl⟩
      map_mul' := fun x y =>
        Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inr ⟨i, x, y, rfl⟩ }
    fun x y => Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inl ⟨i, x, y, rfl⟩
#align ring.direct_limit.of Ring.DirectLimit.of

def lift : DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σi, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σi : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [RingHom.map_sub, lift_of, Hg, RingHom.map_one, RingHom.map_add, RingHom.map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])
#align ring.direct_limit.lift Ring.DirectLimit.lift

def map (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G _ _ x) = of G' (fun _ _ h ↦ f' _ _ h) i (g i x) :=
  lift_of _ _ _ _ _

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun i ↦ RingHom.id _) (fun _ _ _ ↦ rfl) =
    RingHom.id (DirectLimit G fun _ _ h ↦ f _ _ h) :=
  DFunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →+* G' i) (g₂ : (i : ι) → G' i →+* G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [RingHom.comp_assoc, hg₁ i, ← RingHom.comp_assoc, hg₂ i, RingHom.comp_assoc] :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) :=
  DFunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ by simp

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) ≃+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  RingEquiv.ofHomInv
    (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1, of_f])
    (DFunLike.ext _ _ fun x ↦ x.induction_on <| by simp)
    (DFunLike.ext _ _ fun x ↦ x.induction_on <| by simp)

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G _ i g) = of G' (fun _ _ h ↦ f' _ _ h) i (e i g) :=
  map_apply_of _ he _

lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' _ i g) = of G (fun _ _ h ↦ f _ _ h) i ((e i).symm g) := by
  simp only [congr, RingEquiv.ofHomInv_symm_apply, map_apply_of, RingHom.coe_coe]

end functorial

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirected ι (· ≤ ·)] [∀ i, Field (G i)]
variable (f : ∀ i j, i ≤ j → G i → G j)
variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

instance nontrivial [DirectedSystem G fun i j h => f' i j h] :
    Nontrivial (Ring.DirectLimit G fun i j h => f' i j h) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
        change (0 : Ring.DirectLimit G fun i j h => f' i j h) ≠ 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
        rw [(f' i j hij).map_one] at hf
        exact one_ne_zero hf⟩⟩
#align field.direct_limit.nontrivial Field.DirectLimit.nontrivial

def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)
#align field.direct_limit.inv Field.DirectLimit.inv

def field [DirectedSystem G fun i j h => f' i j h] :
    Field (Ring.DirectLimit G fun i j h => f' i j h) :=
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  { inv := inv G fun i j h => f' i j h
    mul_inv_cancel := fun p => DirectLimit.mul_inv_cancel G fun i j h => f' i j h
    inv_zero := dif_pos rfl
    qsmul := qsmulRec _ }
#align field.direct_limit.field Field.DirectLimit.field

structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →ₗ[R] P :=
  liftQ _ (DirectSum.toModule R ι P g)
    (span_le.2 fun a ⟨i, j, hij, x, hx⟩ => by
      rw [← hx, SetLike.mem_coe, LinearMap.sub_mem_ker_iff, DirectSum.toModule_lof,
        DirectSum.toModule_lof, Hg])
#align module.direct_limit.lift Module.DirectLimit.lift

structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap)
    (fun i => (g i).toIntLinearMap) Hg).toAddMonoidHom
#align add_comm_group.direct_limit.lift AddCommGroup.DirectLimit.lift

structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift : DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σi, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σi : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [RingHom.map_sub, lift_of, Hg, RingHom.map_one, RingHom.map_add, RingHom.map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])
#align ring.direct_limit.lift Ring.DirectLimit.lift

structure on the direct limit of fields.
See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def field [DirectedSystem G fun i j h => f' i j h] :
    Field (Ring.DirectLimit G fun i j h => f' i j h) :=
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  { inv := inv G fun i j h => f' i j h
    mul_inv_cancel := fun p => DirectLimit.mul_inv_cancel G fun i j h => f' i j h
    inv_zero := dif_pos rfl
    qsmul := qsmulRec _ }
#align field.direct_limit.field Field.DirectLimit.field