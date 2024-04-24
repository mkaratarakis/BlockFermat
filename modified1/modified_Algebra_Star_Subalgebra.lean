def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.copy S.toSubalgebra s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a ∈ (S : Set A))
  -- Porting note: the old proof kept crashing Lean
#align star_subalgebra.copy StarSubalgebra.copy

def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx
#align star_subalgebra.smul_mem StarSubalgebra.smul_mem

def subtype : S →⋆ₐ[R] A := by refine' { toFun := ((↑) : S → A), .. } <;> intros <;> rfl
#align star_subalgebra.subtype StarSubalgebra.subtype

def inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂ where
  toFun := Subtype.map id h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align star_subalgebra.inclusion StarSubalgebra.inclusion

def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }
#align star_subalgebra.map StarSubalgebra.map

def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := @fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }
#align star_subalgebra.comap StarSubalgebra.comap

def centralizer (s : Set A) : StarSubalgebra R A where
  toSubalgebra := Subalgebra.centralizer R (s ∪ star s)
  star_mem' := Set.star_mem_centralizer
#align star_subalgebra.centralizer StarSubalgebra.centralizer

def starClosure (S : Subalgebra R A) : StarSubalgebra R A where
  toSubalgebra := S ⊔ star S
  star_mem' := fun {a} ha => by
    simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
    rw [← mem_star_iff _ a, star_adjoin_comm, sup_comm]
    simpa using ha
#align subalgebra.star_closure Subalgebra.starClosure

def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s ∪ star s) with
    star_mem' := fun hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }
#align star_subalgebra.adjoin StarAlgebra.adjoin

def gi : GaloisInsertion (adjoin R : Set A → StarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (StarAlgebra.gc.le_u_l s) hs
  gc := StarAlgebra.gc
  le_l_u S := (StarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _
#align star_subalgebra.gi StarAlgebra.gi

def adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSubalgebra.toSemiring with
    mul_comm := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      ext
      simp only [MulMemClass.mk_mul_mk]
      rw [← mem_toSubalgebra, adjoin_toSubalgebra] at hx hy
      letI : CommSemiring (Algebra.adjoin R (s ∪ star s)) :=
        Algebra.adjoinCommSemiringOfComm R
          (by
            intro a ha b hb
            cases' ha with ha ha <;> cases' hb with hb hb
            · exact hcomm _ ha _ hb
            · exact star_star b ▸ hcomm_star _ ha _ hb
            · exact star_star a ▸ (hcomm_star _ hb _ ha).symm
            · simpa only [star_mul, star_star] using congr_arg star (hcomm _ hb _ ha))
      exact congr_arg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin R (s ∪ star s)) ⟨y, hy⟩) }
#align star_subalgebra.adjoin_comm_semiring_of_comm StarAlgebra.adjoinCommSemiringOfComm

def adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A] [Algebra R A]
    [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommRing (adjoin R s) :=
  { StarAlgebra.adjoinCommSemiringOfComm R hcomm hcomm_star,
    (adjoin R s).toSubalgebra.toRing with }
#align star_subalgebra.adjoin_comm_ring_of_comm StarAlgebra.adjoinCommRingOfComm

def equalizer : StarSubalgebra R A :=
  { toSubalgebra := AlgHom.equalizer (f : A →ₐ[R] B) g
    star_mem' := @fun a (ha : f a = g a) => by simpa only [← map_star] using congrArg star ha }
-- Porting note: much like `StarSubalgebra.copy` the old proof was broken and hard to fix
#align star_alg_hom.equalizer StarAlgHom.equalizer

structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
  [StarRing A] [Algebra R A] [StarModule R A] extends Subalgebra R A : Type v where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier
#align star_subalgebra StarSubalgebra

structure -/

end StarAlgebra

namespace StarSubalgebra

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

instance completeLattice : CompleteLattice (StarSubalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice StarAlgebra.gi
  bot := { toSubalgebra := ⊥, star_mem' := fun ⟨r, hr⟩ => ⟨star r, hr ▸ algebraMap_star_comm _⟩ }
  bot_le S := (bot_le : ⊥ ≤ S.toSubalgebra)

instance inhabited : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

@[simp]
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl
#align star_subalgebra.coe_top StarSubalgebra.coe_top