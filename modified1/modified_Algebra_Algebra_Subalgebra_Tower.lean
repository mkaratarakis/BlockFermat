def x
#align algebra.lmul_algebra_map Algebra.lmul_algebraMap

def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebraMap_mem' := fun x ↦ by
      rw [algebraMap_apply R S A]
      exact U.algebraMap_mem _ }
#align subalgebra.restrict_scalars Subalgebra.restrictScalars

def ofRestrictScalars (U : Subalgebra S A) (f : U →ₐ[S] B) : U.restrictScalars R →ₐ[R] B :=
  f.restrictScalars R
#align subalgebra.of_restrict_scalars Subalgebra.ofRestrictScalars