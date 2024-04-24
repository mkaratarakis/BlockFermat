def `RestrictScalars.moduleOrig` if really needed.
* `RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A`: the ring equivalence
   between the restricted and original space when the module is an algebra.

## See also

def RestrictScalars (_R _S M : Type*) : Type _ := M
#align restrict_scalars RestrictScalars

def RestrictScalars.moduleOrig [I : Module S M] : Module S (RestrictScalars R S M) := I
#align restrict_scalars.module_orig RestrictScalars.moduleOrig

def RestrictScalars.lsmul [Module S M] : S →ₐ[R] Module.End R (RestrictScalars R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)
#align restrict_scalars.lsmul RestrictScalars.lsmul

def RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M :=
  AddEquiv.refl M
#align restrict_scalars.add_equiv RestrictScalars.addEquiv

def (c : R) (x : RestrictScalars R S M) :
    c • x = (RestrictScalars.addEquiv R S M).symm
      (algebraMap R S c • RestrictScalars.addEquiv R S M x) :=
  rfl
#align restrict_scalars.smul_def RestrictScalars.smul_def

def RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A :=
  RingEquiv.refl _
#align restrict_scalars.ring_equiv RestrictScalars.ringEquiv

structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `RestrictScalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variable (R S M : Type*)
variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module S M]
```
With the assumptions above we can't directly state our map as we have no `Module R M` structure, but
`RestrictScalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `RestrictScalars` which is compatible
example : RestrictScalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [Module R M] [IsScalarTower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[Module R M] [IsScalarTower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `RestrictScalars` entirely. If not, we can pass
`RestrictScalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`IsScalarTower` rather than `RestrictScalars`.

An example of when one might want to use `RestrictScalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unusedArguments]
def RestrictScalars (_R _S M : Type*) : Type _ := M
#align restrict_scalars RestrictScalars

structure over `R`.

The preferred way of setting this up is `[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
instance RestrictScalars.module [Module S M] : Module R (RestrictScalars R S M) :=
  Module.compHom M (algebraMap R S)

/-- This instance is only relevant when `RestrictScalars.moduleOrig` is available as an instance.
-/
instance RestrictScalars.isScalarTower [Module S M] : IsScalarTower R S (RestrictScalars R S M) :=
  ⟨fun r S M ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
#align restrict_scalars.is_scalar_tower RestrictScalars.isScalarTower

structure over `R`.
The preferred way of setting this up is
`[Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ M] [IsScalarTower Rᵐᵒᵖ Sᵐᵒᵖ M]`.
-/
instance RestrictScalars.opModule [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars R S M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)
#align restrict_scalars.op_module RestrictScalars.opModule