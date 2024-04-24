def PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
  (LinearMap.llcomp R _ _ _ (Fintype.total R R b)).comp algEquivMatrix'.symm.toLinearMap
#align pi_to_module.from_matrix PiToModule.fromMatrix

def PiToModule.fromEnd : Module.End R M →ₗ[R] (ι → R) →ₗ[R] M :=
  LinearMap.lcomp _ _ (Fintype.total R R b)
#align pi_to_module.from_End PiToModule.fromEnd

def Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f
#align matrix.represents Matrix.Represents

def Matrix.isRepresentation : Subalgebra R (Matrix ι ι R) where
  carrier := { A | ∃ f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .algebraMap _⟩
#align matrix.is_representation Matrix.isRepresentation

def Matrix.isRepresentation.toEnd : Matrix.isRepresentation R b →ₐ[R] Module.End R M
    where
  toFun A := A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ := (A₁ + A₂).2.choose_spec.eq hb (A₁.2.choose_spec.add A₂.2.choose_spec)
  commutes' r :=
    (algebraMap _ (Matrix.isRepresentation R b) r).2.choose_spec.eq hb (.algebraMap r)
#align matrix.is_representation.to_End Matrix.isRepresentation.toEnd