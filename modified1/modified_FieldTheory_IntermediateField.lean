def toSubfield : Subfield L :=
  { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }
#align intermediate_field.to_subfield IntermediateField.toSubfield

def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : IntermediateField K L
    where
  toSubalgebra := S.toSubalgebra.copy s (hs : s = S.toSubalgebra.carrier)
  inv_mem' :=
    have hs' : (S.toSubalgebra.copy s hs).carrier = S.toSubalgebra.carrier := hs
    hs'.symm ▸ S.inv_mem'
#align intermediate_field.copy IntermediateField.copy

def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
    IntermediateField K L :=
  { S with
    inv_mem' := inv_mem }
#align subalgebra.to_intermediate_field Subalgebra.toIntermediateField

def Subalgebra.toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : IntermediateField K L :=
  S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    letI hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) ≠ 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff, S.coe_mul, S.coe_one, Subtype.coe_mk, mul_eq_one_iff_inv_eq₀ hx0] at hy
    exact hy.symm ▸ y.2
#align subalgebra.to_intermediate_field' Subalgebra.toIntermediateField'

def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : ∀ x, algebraMap K L x ∈ S) :
    IntermediateField K L :=
  { S with
    algebraMap_mem' := algebra_map_mem }
#align subfield.to_intermediate_field Subfield.toIntermediateField

def comap (f : L →ₐ[K] L') (S : IntermediateField K L') : IntermediateField K L where
  __ := S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ ∈ S by rw [map_inv₀ f x]; exact S.inv_mem hx

/-- Given `f : L →ₐ[K] L'`, `S.map f` is the intermediate field between `K` and `L'`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') (S : IntermediateField K L) : IntermediateField K L' where
  __ := S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩
#align intermediate_field.map IntermediateField.map

def intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K] E.map e.toAlgHom :=
  e.subalgebraMap E.toSubalgebra
#align intermediate_field.intermediate_field_map IntermediateField.intermediateFieldMap

def fieldRange : IntermediateField K L' :=
  { f.range, (f : L →+* L').fieldRange with }
#align alg_hom.field_range AlgHom.fieldRange

def val : S →ₐ[K] L :=
  S.toSubalgebra.val
#align intermediate_field.val IntermediateField.val

def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF
#align intermediate_field.inclusion IntermediateField.inclusion

def lift {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  E.map (val F)
#align intermediate_field.lift IntermediateField.lift

def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }
#align intermediate_field.restrict_scalars IntermediateField.restrictScalars

def extendScalars : IntermediateField F L := E.toSubfield.toIntermediateField fun ⟨_, hf⟩ ↦ h hf

@[simp]
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_extendScalars : x ∈ extendScalars h ↔ x ∈ E := Iff.rfl

@[simp]
theorem extendScalars_restrictScalars : (extendScalars h).restrictScalars K = E := rfl

theorem extendScalars_le_extendScalars_iff : extendScalars h ≤ extendScalars h' ↔ E ≤ E' := Iff.rfl

theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h ≤ E' ↔ E ≤ E'.restrictScalars K := Iff.rfl

theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' ≤ extendScalars h ↔ E'.restrictScalars K ≤ E := Iff.rfl

variable (F)

/-- `IntermediateField.extendScalars` is an order isomorphism from
`{ E : IntermediateField K L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.restrictScalars`. -/
def extendScalars.orderIso : { E : IntermediateField K L // F ≤ E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩⟩
  left_inv E := rfl
  right_inv E := rfl
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

theorem extendScalars_injective :
    Function.Injective fun E : { E : IntermediateField K L // F ≤ E } ↦ extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end ExtendScalars

end Tower

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F :=
  left K F L
#align intermediate_field.finite_dimensional_left IntermediateField.finiteDimensional_left

def subalgebraEquivIntermediateField (alg : Algebra.IsAlgebraic K L) :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl
#align subalgebra_equiv_intermediate_field subalgebraEquivIntermediateField

structure extending `Subfield` and `Subalgebra`.
A `Subalgebra` is closed under all operations except `⁻¹`,

## Tags

structure IntermediateField extends Subalgebra K L where
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier
#align intermediate_field IntermediateField

structure -/
instance toField : Field S :=
  S.toSubfield.toField
#align intermediate_field.to_field IntermediateField.toField

structure from their `Subalgebra` coercions. -/


instance module' {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  S.toSubalgebra.module'
#align intermediate_field.module' IntermediateField.module'