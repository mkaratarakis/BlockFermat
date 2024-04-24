def adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)
#align orthonormal_basis.adjust_to_orientation OrthonormalBasis.adjustToOrientation

def finOrthonormalBasis (hn : 0 < n) (h : finrank ℝ E = n) (x : Orientation ℝ E (Fin n)) :
    OrthonormalBasis (Fin n) ℝ E := by
  haveI := Fin.pos_iff_nonempty.1 hn
  haveI : FiniteDimensional ℝ E := .of_finrank_pos <| h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x
#align orientation.fin_orthonormal_basis Orientation.finOrthonormalBasis

def volumeForm : E [⋀^Fin n]→ₗ[ℝ] ℝ := by
  classical
    cases' n with n
    · let opos : E [⋀^Fin 0]→ₗ[ℝ] ℝ := .constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
      exact o.eq_or_eq_neg_of_isEmpty.by_cases (fun _ => opos) fun _ => -opos
    · exact (o.finOrthonormalBasis n.succ_pos _i.out).toBasis.det
#align orientation.volume_form Orientation.volumeForm