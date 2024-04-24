def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1
#align parallelepiped parallelepiped

def Basis.parallelepiped (b : Basis ι ℝ E) : PositiveCompacts E where
  carrier := _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finset_sum Finset.univ fun (i : ι) (_H : i ∈ Finset.univ) =>
        (continuous_apply i).smul continuous_const)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only [_root_.parallelepiped]
      convert H
      exact (b.equivFun_symm_apply _).symm
    have A : Set.Nonempty (interior (Icc (0 : ι → ℝ) 1)) := by
      rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, image_nonempty]
#align basis.parallelepiped Basis.parallelepiped

def Basis.addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped
#align basis.add_haar Basis.addHaar

def measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) where
  toEquiv := WithLp.equiv _ _
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align euclidean_space.measurable_equiv EuclideanSpace.measurableEquiv

structure
on `EuclideanSpace`. -/


namespace EuclideanSpace

variable (ι)

-- TODO: do we want these instances for `PiLp` too?
instance : MeasurableSpace (EuclideanSpace ℝ ι) := MeasurableSpace.pi

instance [Finite ι] : BorelSpace (EuclideanSpace ℝ ι) := Pi.borelSpace

/-- `WithLp.equiv` as a `MeasurableEquiv`. -/
@[simps toEquiv]
protected def measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) where
  toEquiv := WithLp.equiv _ _
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align euclidean_space.measurable_equiv EuclideanSpace.measurableEquiv