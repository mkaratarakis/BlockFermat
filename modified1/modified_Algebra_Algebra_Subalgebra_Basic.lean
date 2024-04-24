def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }
#align subalgebra.copy Subalgebra.copy

def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[aesop safe apply (rule_sets := [SetLike])]
theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r ∈ s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  algebraMap_mem S r
#align subalgebra.algebra_map_mem Subalgebra.algebraMap_mem

def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid
#align subalgebra.to_add_submonoid Subalgebra.toAddSubmonoid

def toSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
--     (S : Subalgebra R A) : Submonoid A :=
--   S.toSubsemiring.toSubmonoid
set_option align.precheck false in
#align subalgebra.to_submonoid Subalgebra.toSubmonoid

def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }
#align subalgebra.to_subring Subalgebra.toSubring

def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx ↦
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h ↦ ext fun x ↦ SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align subalgebra.to_submodule Subalgebra.toSubmodule

def _ _ }
#align subalgebra.algebra' Subalgebra.algebra'

def val : S →ₐ[R] A :=
  { toFun := ((↑) : S → A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }
#align subalgebra.val Subalgebra.val

def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl
#align subalgebra.to_submodule_equiv Subalgebra.toSubmoduleEquiv

def map (f : A →ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }
#align subalgebra.map Subalgebra.map

def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }
#align subalgebra.comap Subalgebra.comap

def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p)
    (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy ↦ h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }
#align submodule.to_subalgebra Submodule.toSubalgebra

def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }
#align alg_hom.range AlgHom.range

def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.eq <| f.commutes r }
#align alg_hom.cod_restrict AlgHom.codRestrict

def rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self
#align alg_hom.range_restrict AlgHom.rangeRestrict

def equalizer (ϕ ψ : A →ₐ[R] B) : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, ϕ.map_add, ψ.map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, ϕ.map_mul, ψ.map_mul, hx, hy]
  algebraMap_mem' x := by rw [Set.mem_setOf_eq, AlgHom.commutes, AlgHom.commutes]
#align alg_hom.equalizer AlgHom.equalizer

def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align alg_equiv.of_left_inverse AlgEquiv.ofLeftInverse

def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)
#align alg_equiv.of_injective AlgEquiv.ofInjective

def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
    [Algebra R E] [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.injective
#align alg_equiv.of_injective_field AlgEquiv.ofInjectiveField

def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A →ₐ[R] B) :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by
      ext; dsimp only; erw [RingEquiv.subsemiringMap_apply_coe]
      exact e.commutes _ }
#align alg_equiv.subalgebra_map AlgEquiv.subalgebraMap

def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }
#align algebra.adjoin Algebra.adjoin

def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _
#align algebra.gi Algebra.gi

def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top
#align algebra.to_top Algebra.toTop

def botEquivOfInjective (h : Function.Injective (algebraMap R A)) :
    (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy : _), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.eq hx⟩⟩
#align algebra.bot_equiv_of_injective Algebra.botEquivOfInjective

def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)
#align algebra.bot_equiv Algebra.botEquiv

def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl <| AlgHom.ext fun _ => Subtype.ext rfl
#align subalgebra.top_equiv Subalgebra.topEquiv

def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T
    where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl
#align subalgebra.inclusion Subalgebra.inclusion

def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where
  __ := LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl
#align subalgebra.equiv_of_eq Subalgebra.equivOfEq

def equivMapOfInjective : S ≃ₐ[R] S.map f :=
  (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]
theorem coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = f x := rfl

end equivMapOfInjective

section Prod

variable (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }
#align subalgebra.prod Subalgebra.prod

def iSupLift : ↥T →ₐ[R] B :=
  { toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
        (fun i j x hxi hxj => by
          let ⟨k, hik, hjk⟩ := dir i j
          dsimp
          rw [hf i k hik, hf j k hjk]
          rfl)
        T (by rw [hT, coe_iSup_of_directed dir])
    map_one' := by apply Set.iUnionLift_const _ (fun _ => 1) <;> simp
    map_zero' := by dsimp; apply Set.iUnionLift_const _ (fun _ => 0) <;> simp
    map_mul' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      all_goals simp
    map_add' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      all_goals simp
    commutes' := fun r => by
      dsimp
      apply Set.iUnionLift_const _ (fun _ => algebraMap R _ r) <;> simp }
#align subalgebra.supr_lift Subalgebra.iSupLift

def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl
#align subalgebra.smul_def Subalgebra.smul_def

def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }
#align subalgebra.center Subalgebra.center

def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }
#align subalgebra.centralizer Subalgebra.centralizer

def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebraMap_mem' := fun i => natCast_mem S i }
#align subalgebra_of_subsemiring subalgebraOfSubsemiring

def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simpa using S.zero_mem)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_one]
          exact S.sub_mem ih S.one_mem }
#align subalgebra_of_subring subalgebraOfSubring

structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] extends
  Subsemiring A : Type v where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1
#align subalgebra Subalgebra

structure from their `Subsemiring` / `Semiring` coercions. -/


instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring
#align subalgebra.to_semiring Subalgebra.toSemiring

structure from their `Submodule` coercions. -/


instance (priority := low) module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  S.toSubmodule.module'
#align subalgebra.module' Subalgebra.module'