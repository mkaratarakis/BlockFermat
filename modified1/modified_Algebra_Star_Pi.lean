def [∀ i, Star (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl
#align pi.star_def Pi.star_def

structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, Star (f i)] : Star (∀ i, f i) where star x i := star (x i)

@[simp]
theorem star_apply [∀ i, Star (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl
#align pi.star_apply Pi.star_apply