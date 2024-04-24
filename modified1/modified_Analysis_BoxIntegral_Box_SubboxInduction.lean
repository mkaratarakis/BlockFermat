def splitCenterBox (I : Box ι) (s : Set ι) : Box ι where
  lower := s.piecewise (fun i ↦ (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i ↦ (I.lower i + I.upper i) / 2
  lower_lt_upper i := by
    dsimp only [Set.piecewise]
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]
#align box_integral.box.split_center_box BoxIntegral.Box.splitCenterBox

def splitCenterBoxEmb (I : Box ι) : Set ι ↪ Box ι :=
  ⟨splitCenterBox I, injective_splitCenterBox I⟩
#align box_integral.box.split_center_box_emb BoxIntegral.Box.splitCenterBoxEmb