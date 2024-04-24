def subtype (s : S) : s →ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

@[simp]
theorem coeSubtype : (subtype s : s → A) = ((↑) : s → A) :=
  rfl

end NonUnitalSubalgebraClass

end NonUnitalSubalgebraClass

/-- A non-unital subalgebra is a sub(semi)ring that is also a submodule. -/
structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    extends NonUnitalSubsemiring A, Submodule R A : Type v

/-- Reinterpret a `NonUnitalSubalgebra` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubalgebra` as a `Submodule`. -/
add_decl_doc NonUnitalSubalgebra.toSubmodule

namespace NonUnitalSubalgebra

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

section NonUnitalNonAssocSemiring
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]

instance : SetLike (NonUnitalSubalgebra R A) A
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where
  smul_mem := @fun s => s.smul_mem'

theorem mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl

theorem toNonUnitalSubsemiring_injective :
    Function.Injective
      (toNonUnitalSubsemiring : NonUnitalSubalgebra R A → NonUnitalSubsemiring A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubsemiring, ← mem_toNonUnitalSubsemiring, h]

theorem toNonUnitalSubsemiring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = U.toNonUnitalSubsemiring ↔ S = U :=
  toNonUnitalSubsemiring_injective.eq_iff

theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : NonUnitalSubalgebra R A → Submodule R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubmodule, ← mem_toSubmodule, h]

theorem toSubmodule_inj {S U : NonUnitalSubalgebra R A} : S.toSubmodule = U.toSubmodule ↔ S = U :=
  toSubmodule_injective.eq_iff

/-- Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' := fun r a (ha : a ∈ s) => by
      show r • a ∈ s
      rw [hs] at ha ⊢
      exact S.smul_mem' r ha }

@[simp]
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

instance (S : NonUnitalSubalgebra R A) : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]
variable [Module R A] [Module R B] [Module R C]

instance instNonUnitalSubringClass : NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
  { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := @fun _ x hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

/-- A non-unital subalgebra over a ring is also a `Subring`. -/
def toNonUnitalSubring (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

@[simp]
theorem mem_toNonUnitalSubring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

theorem toNonUnitalSubring_injective :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

theorem toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

end NonUnitalNonAssocRing

section

/-! `NonUnitalSubalgebra`s inherit structure from their `NonUnitalSubsemiring` / `Semiring`
coercions. -/


instance toNonUnitalNonAssocSemiring [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocSemiring S :=
  inferInstance

instance toNonUnitalSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

instance toNonUnitalCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

instance toNonUnitalNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocRing S :=
  inferInstance

instance toNonUnitalRing [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance

instance toNonUnitalCommRing [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance

end

/-- The forgetful map from `NonUnitalSubalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubsemiring' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubring' [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]
variable {S : NonUnitalSubalgebra R A}

section

/-! ### `NonUnitalSubalgebra`s inherit structure from their `Submodule` coercions. -/

structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    extends NonUnitalSubsemiring A, Submodule R A : Type v

/-- Reinterpret a `NonUnitalSubalgebra` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubalgebra` as a `Submodule`. -/
add_decl_doc NonUnitalSubalgebra.toSubmodule

namespace NonUnitalSubalgebra

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

section NonUnitalNonAssocSemiring
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]

instance : SetLike (NonUnitalSubalgebra R A) A
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where
  smul_mem := @fun s => s.smul_mem'

theorem mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl

theorem toNonUnitalSubsemiring_injective :
    Function.Injective
      (toNonUnitalSubsemiring : NonUnitalSubalgebra R A → NonUnitalSubsemiring A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubsemiring, ← mem_toNonUnitalSubsemiring, h]

theorem toNonUnitalSubsemiring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = U.toNonUnitalSubsemiring ↔ S = U :=
  toNonUnitalSubsemiring_injective.eq_iff

theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : NonUnitalSubalgebra R A → Submodule R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubmodule, ← mem_toSubmodule, h]

theorem toSubmodule_inj {S U : NonUnitalSubalgebra R A} : S.toSubmodule = U.toSubmodule ↔ S = U :=
  toSubmodule_injective.eq_iff

/-- Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' := fun r a (ha : a ∈ s) => by
      show r • a ∈ s
      rw [hs] at ha ⊢
      exact S.smul_mem' r ha }

@[simp]
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

instance (S : NonUnitalSubalgebra R A) : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]
variable [Module R A] [Module R B] [Module R C]

instance instNonUnitalSubringClass : NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
  { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := @fun _ x hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

/-- A non-unital subalgebra over a ring is also a `Subring`. -/
def toNonUnitalSubring (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

@[simp]
theorem mem_toNonUnitalSubring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

theorem toNonUnitalSubring_injective :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

theorem toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

end NonUnitalNonAssocRing

section

/-! `NonUnitalSubalgebra`s inherit structure from their `NonUnitalSubsemiring` / `Semiring`
coercions. -/


instance toNonUnitalNonAssocSemiring [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocSemiring S :=
  inferInstance

instance toNonUnitalSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

instance toNonUnitalCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

instance toNonUnitalNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocRing S :=
  inferInstance

instance toNonUnitalRing [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance

instance toNonUnitalCommRing [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance

end

/-- The forgetful map from `NonUnitalSubalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubsemiring' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubring' [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]
variable {S : NonUnitalSubalgebra R A}

section

/-! ### `NonUnitalSubalgebra`s inherit structure from their `Submodule` coercions. -/